module Equality where

data _≡_ {T : Set} : T → T → Set where
  refl : {x : T} → x ≡ x

infix 2 _≡_
