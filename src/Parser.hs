module Parser (Parser.parse) where

import Control.Monad (void, when)
import Control.Monad.Combinators.Expr (Operator (..), makeExprParser)
import Data.ByteString.Lazy (ByteString)
import Data.Char (isAlphaNum)
import Data.Text qualified as Strict
import Data.Text.Lazy qualified as Lazy
import Data.Text.Lazy.Encoding qualified as Lazy
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as Lexer

import Syntax

type Parser = Parsec Error Lazy.Text

newtype Error = KeywordAsIdentifier Strict.Text
  deriving stock (Eq, Ord)

instance ShowErrorComponent Error where
  showErrorComponent (KeywordAsIdentifier s) = concat ["keyword `", Strict.unpack s, "`used as identifier"]

parse :: FilePath -> ByteString -> Either String [Expr]
parse fp src = case runParser file fp (Lazy.decodeUtf8 src) of
  Left errs -> Left (errorBundlePretty errs)
  Right xs -> Right xs

file :: Parser [Expr]
file = sc *> many stmt <* eof

stmt :: Parser Expr
stmt = do
  x <- expr
  case x of
    Cond {} -> pure ()
    While {} -> pure ()
    For {} -> pure ()
    Fun {} -> pure ()
    Block {} -> pure ()
    _ -> symbol ";"
  pure x

typ :: Parser Type
typ =
  choice
    [ TUnit <$ symbol "()"
    , TBool <$ symbol "bool"
    , TInt <$ symbol "int"
    , TFloat <$ symbol "float"
    , TString <$ symbol "string"
    , tArray
    , tObject
    , tFunction
    ]

tArray :: Parser Type
tArray = do
  symbol "["
  ty <- typ
  symbol "]"
  pure (TArray ty)

tObject :: Parser Type
tObject = do
  symbol "{"
  fields <- entry typ ":" `sepEndBy` symbol ","
  symbol "}"
  pure (TObject fields)

tFunction :: Parser Type
tFunction = do
  symbol "fun"
  symbol "("
  params <- typ `sepEndBy` symbol ","
  symbol ")"
  symbol "->"
  retTy <- typ
  pure (TFunction params retTy)

expr :: Parser Expr
expr = makeExprParser atom ops
  where
    ops =
      [ [postfixes]
      , [inL Times "*" "=", inL Divide "/" "=", inL Mod "%" "="]
      , [inL Plus "+" "+=", inL Minus "-" "="]
      , [inR Append "++" ""]
      , [inL Lt "<" "=", inL Lte "<=" "", inL Gt ">" "=", inL Gte ">=" ""]
      , [inL Eq "==" "", inL Neq "!=" ""]
      , [inR And "&&" ""]
      , [inR Or "||" ""]
      , [assign, comp Plus "+=", comp Minus "-=", comp Times "*=", comp Divide "/=", comp Mod "%="]
      ]
    inL = inf InfixL
    inR = inf InfixR
    inf p op sym sfxs = p do
      try $ lexeme do
        _ <- string sym
        notFollowedBy (choice (map char sfxs))
      pure (BinOp op)
    postfixes = Postfix $ foldr1 (flip (.)) <$> some (choice [call, subscript, access])
    call = do
      symbol "("
      args <- expr `sepEndBy` symbol ","
      symbol ")"
      pure \f -> Call f args
    subscript = do
      symbol "["
      ix <- expr
      symbol "]"
      pure \xs -> Subscript xs ix
    access = do
      try (symbol "." *> notFollowedBy (char '}'))
      field <- ident
      pure \obj -> Access obj field
    assign = InfixR do
      try $ lexeme do
        _ <- char '='
        notFollowedBy (char '=')
      pure (Assign Nothing)
    comp op sym = InfixR do
      symbol sym
      pure (Assign (Just op))

atom :: Parser Expr
atom =
  choice
    [ unit <?> "unit"
    , hidden $ between "(" ")" expr
    , bool <?> "boolean"
    , number <?> "number"
    , str <?> "string"
    , array <?> "array"
    , object <?> "object"
    , lambda <?> "lambda"
    , ret <?> "return"
    , cond <?> "conditional"
    , while <?> "while loop"
    , for <?> "for loop"
    , hidden decl
    , hidden fun
    , hidden alias
    , block <?> "block"
    , var <?> "variable"
    ]

unit :: Parser Expr
unit = Unit <$ symbol "()"

bool :: Parser Expr
bool = Bool False <$ symbol "false" <|> Bool True <$ symbol "true"

number :: Parser Expr
number = lexeme (try float <|> int)
  where
    int = Int <$> Lexer.decimal
    float = Float <$> Lexer.float

str :: Parser Expr
str = lexeme do
  _ <- char '\"'
  cs <- manyTill Lexer.charLiteral (char '\"')
  pure (String (Strict.pack cs))

array :: Parser Expr
array = do
  symbol "["
  elems <- expr `sepEndBy` symbol ","
  symbol "]"
  pure (Array elems)

object :: Parser Expr
object = do
  symbol "{."
  fields <- entry expr "=" `sepEndBy` symbol ","
  symbol ".}"
  pure (Object fields)

lambda :: Parser Expr
lambda = do
  symbol "|"
  params <- entry typ ":" `sepEndBy` symbol ","
  symbol "|"
  symbol "->"
  retTy <- typ
  body <- block
  pure (Lambda params retTy body)

ret :: Parser Expr
ret = do
  symbol "return"
  value <- optional expr
  pure (Return value)

cond :: Parser Expr
cond = do
  symbol "if"
  symbol "("
  b <- expr
  symbol ")"
  true <- block
  false <- optional do
    symbol "else"
    cond <|> block
  pure (Cond b true false)

while :: Parser Expr
while = do
  symbol "while"
  symbol "("
  b <- expr
  symbol ")"
  body <- block
  pure (While b body)

for :: Parser Expr
for = do
  symbol "for"
  symbol "("
  name <- ident
  symbol ":"
  ty <- typ
  symbol "in"
  xs <- expr
  symbol ")"
  body <- block
  pure (For name ty xs body)

decl :: Parser Expr
decl = do
  symbol "let"
  name <- ident
  symbol ":"
  ty <- typ
  symbol "="
  body <- expr
  pure (Decl name ty body)

fun :: Parser Expr
fun = do
  symbol "fun"
  name <- ident
  symbol "("
  params <- entry typ ":" `sepEndBy` symbol ","
  symbol ")"
  symbol "->"
  retTy <- typ
  body <- block
  pure (Fun name params retTy body)

alias :: Parser Expr
alias = do
  symbol "type"
  name <- ident
  symbol "="
  body <- typ
  pure (Alias name body)

block :: Parser Expr
block = do
  symbol "{"
  stmts <- many stmt
  symbol "}"
  pure (Block stmts)

var :: Parser Expr
var = Var <$> ident

entry :: Parser a -> Lazy.Text -> Parser (Strict.Text, a)
entry p sep = do
  name <- ident
  symbol sep
  x <- p
  pure (name, x)

ident :: Parser Strict.Text
ident = lexeme do
  c <- letterChar
  cs <- takeWhileP Nothing (\x -> isAlphaNum x || x == '_')
  let s = Lazy.toStrict (c `Lazy.cons` cs)
  when (s `elem` keywords) do
    customFailure (KeywordAsIdentifier s)
  pure s
  where
    keywords = ["false", "true", "let", "if", "else", "while", "for", "in", "fun", "type"]

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme sc

symbol :: Lazy.Text -> Parser ()
symbol = void . Lexer.symbol sc

sc :: Parser ()
sc = Lexer.space space1 (Lexer.skipLineComment "//") (Lexer.skipBlockCommentNested "/*" "*/")
