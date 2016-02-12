module Error where
open import Char
open import Nat
open import Instr
open import String

data Error : Set where
  ExpectedChar : Character → Character → Error
  UnexpectedChar : Character → Error
  ApplicationError : {n : ℕ} → Operator n → Error
  EmptyPop : Error
  EmptyApply : Error

showErr : Error → String
showErr (ExpectedChar x y) = "Parse Error: Expected " ^ (showChar x) ^ ", found '" ^ (showChar y)
showErr (UnexpectedChar x) = "Parse Error: Unexpected " ^ (showChar x)
showErr (ApplicationError x) = "Error attempting to apply '" ^ (showOp x) ^ "'"
showErr EmptyPop = "Error attempting to pop empty stack"
showErr EmptyApply = "Error attempting to apply empty stack"
