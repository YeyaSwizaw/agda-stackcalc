module Char where
open import Nat

postulate
  Character : Set

{-# BUILTIN CHAR Character #-}

primitive
  primCharToNat : Character → ℕ
