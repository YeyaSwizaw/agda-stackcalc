module String where
open import Char
open import Nat
open import List

postulate
  String : Set

{-# BUILTIN STRING String #-}

primitive
  primStringToList : String → List Character
  primShowInteger : Integer → String

showNat : ℕ → String
showNat n = primShowInteger (primNatToInteger n)
