module Syntax where

import Data.Text (Text)

type Name = Text

type Field = Text

data Type
  = TUnit
  | TBool
  | TInt
  | TFloat
  | TString
  | TArray Type
  | TObject [(Field, Type)]
  | TFunction [Type] Type
  deriving stock (Show, Eq)

data Expr
  = Unit
  | Bool Bool
  | Int Int
  | Float Double
  | String Text
  | Array [Expr]
  | Object [(Field, Expr)]
  | Lambda [(Name, Type)] Type Expr
  | Var Name
  | Call Expr [Expr]
  | Subscript Expr Expr
  | Access Expr Field
  | BinOp BinOp Expr Expr
  | Cond Expr Expr (Maybe Expr)
  | While Expr Expr
  | For Name Type Expr Expr
  | Return (Maybe Expr)
  | Decl Name Type Expr
  | Fun Name [(Name, Type)] Type Expr
  | Alias Name Type
  | Assign (Maybe BinOp) Expr Expr
  | Block [Expr]
  deriving stock (Show)

data BinOp
  = Plus
  | Minus
  | Times
  | Divide
  | Mod
  | Lt
  | Lte
  | Neq
  | Eq
  | Gte
  | Gt
  | And
  | Or
  | Append
  deriving stock (Show)
