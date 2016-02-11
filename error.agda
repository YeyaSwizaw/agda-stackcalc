module Error where
open import Char
open import Nat
open import Instr

data Error : Set where
  ExpectedChar : Character → Character → Error
  UnexpectedChar : Character → Error
  ApplicationError : {n : ℕ} → Operator n → Error
  EmptyPop : Error
  EmptyApply : Error
