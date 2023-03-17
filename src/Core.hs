module Core (
  -- * Names
  Name,
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
import Data.Text qualified as Text
import Prettyprinter (Pretty (..), (<+>))
import Prettyprinter qualified as PP

import Syntax (Field, Type (..))

type Name = Int

type Stmt = Expr

data Expr
  = Unit
  | Bool Bool
  | Int !Int
  | Float !Double
  | String Text
  | Lambda [Name] Expr
  | Intrinsic Intrinsic
  | Val !Name
  | Var !Name
  | Call Expr [Expr]
  | Cond Expr Expr Expr
  | While Expr [Stmt]
  | Return Expr
  | Assign !Name Expr
  | Decl !Name Expr
  | Bind !Name Expr
  | Block [Stmt] Expr

data Number = NInt | NFloat
  deriving stock (Eq, Ord)

data Arith = Plus | Minus | Times | Divide
  deriving stock (Eq, Ord)

data Comparison = Lt | Lte | Eq | Neq | Gte | Gt
  deriving stock (Eq, Ord)

data Logic = And | Or
  deriving stock (Eq, Ord)

data Intrinsic
  = Arith Arith Number
  | Modulo
  | Cast Number Number
  | Compare Comparison Number
  | Logic Logic
  | StringAppend
  | NewArray Type
  | ArrayLength Type
  | ReadArray Type
  | WriteArray Type
  | NewObject
  | ReadObject Field
  | WriteObject Field
  | ToString Type
  | WriteStdout
  | ReadStdinLine
  deriving stock (Eq, Ord)

instance Pretty Expr where
  pretty = \case
    Unit -> "()"
    Bool True -> "true"
    Bool False -> "false"
    Int x -> pretty x
    Float x -> pretty x
    String s -> pretty (show (Text.unpack s))
    Lambda params body -> "|" <> sep "x" params <> "|" <+> pretty body
    Intrinsic x -> pretty x
    Val n -> "x" <> pretty n
    Var n -> "v" <> pretty n
    Call f args -> pretty f <> PP.parens (sep "" args)
    Cond cond true false -> "if" <+> PP.parens (pretty cond) <+> pretty true <+> "else" <+> pretty false
    While cond body -> "while" <+> PP.parens (pretty cond) <+> PP.nest 2 (PP.vsep ("{" : (pretty <$> body))) <> PP.line <> "}"
    Return value -> "return" <+> pretty value
    Assign n value -> "*v" <> pretty n <+> "=" <+> pretty value
    Decl n value -> "var" <+> "v" <> pretty n <+> "=" <+> pretty value
    Bind n value -> "const" <+> "x" <> pretty n <+> "=" <+> pretty value
    Block ss x -> PP.nest 2 (PP.vsep ("{" : (pretty <$> ss) ++ [pretty x])) <> PP.line <> "}"
    where
      sep :: Pretty a => PP.Doc ann -> [a] -> PP.Doc ann
      sep s xs = PP.hsep (PP.punctuate "," ((s <>) . pretty <$> xs))

instance Pretty Intrinsic where
  pretty = \case
    Arith op n -> pretty op <> "_" <> pretty n
    Modulo -> "mod"
    Cast n n' -> pretty n <> "_to_" <> pretty n'
    Compare cmp n -> pretty cmp <> "_" <> pretty n
    Logic op -> "logical_" <> pretty op
    StringAppend -> "string_append"
    NewArray ty -> "new_" <> pretty ty <> "_array"
    ArrayLength ty -> "array_length_" <> pretty ty
    ReadArray ty -> "read_" <> pretty ty <> "_array"
    WriteArray ty -> "write_" <> pretty ty <> "_array"
    NewObject -> "new_object"
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
