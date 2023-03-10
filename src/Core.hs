module Core (
  -- * Names
  Name (..),
  Tag (..),
  zeroTag,
  incTag,
  Field,

  -- * Expressions
  Type (..),
  Stmt,
  Expr (..),

  -- * Intrinsics
  Intrinsic (..),
  Arith (..),
  Comparison (..),
  Logic (..),
  Number (..),
)
where

import Data.Text (Text)
import Prettyprinter (Pretty (..), Doc, (<+>))
import Prettyprinter qualified as PP

import Syntax (Field, Type (..))

data Name
  = Name !Tag
  | Intrinsic Intrinsic

newtype Tag = Tag Int

zeroTag :: Tag
zeroTag = Tag 0

incTag :: Tag -> Tag
incTag (Tag x) = Tag (x + 1)

type Stmt = Expr

data Expr
  = Unit
  | Bool !Bool
  | Int !Int
  | Float !Double
  | String Text
  | Array Type [Expr]
  | Object [(Field, Expr)]
  | Lambda [Tag] [Tag] Expr
  | Var Name
  | Call Expr [Expr]
  | Cond Expr Expr Expr
  | Loop Expr [Stmt]
  | Return Expr
  | Decl Tag Expr
  | Assign Tag Expr
  | Block [Stmt] Expr

data Number = NInt | NFloat

data Arith = Plus | Minus | Times | Divide

data Comparison = Lt | Lte | Eq | Neq | Gte | Gt

data Logic = And | Or

data Intrinsic
  = Arith Arith Number
  | Modulo
  | Cast Number Number
  | Compare Comparison Number
  | Logic Logic
  | StringAppend
  | ArrayLength Type
  | ReadArray Type
  | WriteArray Type
  | ReadObject Field
  | WriteObject Field
  | ToString Type
  | WriteStdout
  | ReadStdinLine

instance Pretty Expr where
  pretty = \case
    Unit -> "()"
    Bool True -> "true"
    Bool False -> "false"
    Int x -> pretty x
    Float x -> pretty x
    String s -> PP.dquotes (pretty s)
    Array _ xs -> "[" <> PP.hsep (PP.punctuate PP.comma (pretty <$> xs)) <> "]"
    Object fields -> PP.nest 2 (PP.vsep ("{." : (field <$> fields))) <> PP.line <> ".}"
      where
        field (n, x) = pretty n <+> "=" <+> pretty x
    Lambda captures params body -> "|" <> commaSep params <> "|" <+> PP.brackets (commaSep captures) <+> pretty body
    Var n -> pretty n
    Call f args -> pretty f <> PP.parens (commaSep args)
    Cond cond true false -> "if" <+> PP.parens (pretty cond) <+> pretty true <+> "else" <+> pretty false
    Loop cond body -> "while" <+> PP.parens (pretty cond) <+> PP.nest 2 (PP.vsep ("{" : (pretty <$> body))) <> PP.line <> "}"
    Return value -> "return" <+> pretty value
    Decl n value -> "let" <+> pretty n <+> "=" <+> pretty value
    Assign n value -> pretty n <+> "=" <+> pretty value
    Block ss x -> PP.nest 2 (PP.vsep ("{" : (pretty <$> ss) ++ [pretty x])) <> PP.line <> "}"
    where
      commaSep :: Pretty a => [a] -> Doc ann
      commaSep = PP.hsep . PP.punctuate PP.comma . fmap pretty

instance Pretty Name where
  pretty = \case
    Name t -> pretty t
    Intrinsic f -> case f of
      Arith op n -> pretty op <> "_" <> pretty n
      Modulo -> "mod"
      Cast n n' -> pretty n <> "_to_" <> pretty n'
      Compare cmp n -> pretty cmp <> "_" <> pretty n
      Logic op -> "logical_" <> pretty op
      StringAppend -> "string_append"
      ArrayLength ty -> "array_length_" <> pretty ty
      ReadArray ty -> "read_" <> pretty ty <> "_array"
      WriteArray ty -> "write_" <> pretty ty <> "_array"
      ReadObject field -> "read_field_" <> pretty field
      WriteObject field -> "write_field_" <> pretty field
      ToString ty -> pretty ty <> "_to_string"
      WriteStdout -> "print"
      ReadStdinLine -> "readLine"

instance Pretty Comparison where
  pretty = \case
    Lt -> "lt"
    Lte -> "lte"
    Eq -> "eq"
    Neq -> "neq"
    Gte -> "gte"
    Gt -> "gt"

instance Pretty Logic where
  pretty = \case
    And -> "and"
    Or -> "or"

instance Pretty Tag where
  pretty (Tag x) = "v" <> pretty x

instance Pretty Type where
  pretty = \case
    TUnit -> "()"
    TBool -> "bool"
    TInt -> "int"
    TFloat -> "float"
    TString -> "string"
    TArray ty -> "[" <> pretty ty <> "]"
    TObject _ -> _ppObj
    TFunction _ _ -> _ppFun

instance Pretty Arith where
  pretty = \case
    Plus -> "plus"
    Minus -> "minus"
    Times -> "times"
    Divide -> "divide"

instance Pretty Number where
  pretty = \case
    NInt -> "int"
    NFloat -> "float"
