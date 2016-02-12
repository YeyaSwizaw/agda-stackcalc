module String where
open import Char
open import Nat
open import List

postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

primitive
  primStringToList : String → List Character
  primShowChar : Character → String
  primShowInteger : Integer → String

showNat : ℕ → String
showNat n = primShowInteger (primNatToInteger n)

showChar : Character → String
showChar c = primShowChar c
