module String where
open import Char
open import Nat
open import Instr
open import List

postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

primitive
  primStringAppend : String → String → String
  primStringToList : String → List Character
  primShowChar : Character → String
  primShowInteger : Integer → String

showNat : ℕ → String
showNat n = primShowInteger (primNatToInteger n)

showChar : Character → String
showChar c = primShowChar c

showOp : {n : ℕ} → Operator n → String
showOp Plus = "+"
showOp Mul = "*"

_^_ : String → String → String
_^_ = primStringAppend

infixr 6 _^_
