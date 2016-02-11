module Instr where
open import Char
open import Nat

data Operator : ℕ → Set where
  Plus : Operator 2
  Mul : Operator 2

data Operatable : Set where
  Char : Character → Operatable
  Int : ℕ → Operatable

data Value : Set where
  Val : Operatable → Value
  Op : (n : ℕ) → Operator n → Value

data Instr : Set where
  Push : Value → Instr
  Pop : Instr
  Apply : Instr

n-ary : ℕ → Set → Set
n-ary 0 T = T
n-ary (suc n) T = T → n-ary n T

op-fn-t : (n : ℕ) → Operator n → Set
op-fn-t n _ = n-ary n ℕ

op-fn : (n : ℕ) → (op : Operator n) → op-fn-t n op
op-fn .2 Plus = _+_
op-fn .2 Mul = _*_

as-nat : Operatable → ℕ
as-nat (Char x) = primCharToNat x
as-nat (Int x) = x
