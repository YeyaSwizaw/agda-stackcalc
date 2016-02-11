module Nat where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

{-# BUILTIN NATPLUS _+_ #-}

_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + (x * y)

{-# BUILTIN NATTIMES _*_ #-}

infixl 5 _+_
infixl 4 _*_

postulate
  Integer : Set

{-# BUILTIN INTEGER Integer #-}

primitive
  primNatToInteger : ℕ → Integer
