module Monad where

module Base where
  data Monad (M : Set → Set) : Set₁ where
    monad : (return : {T : Set} → T → M T) → (bind : {T U : Set} → M T → (T → M U) → M U) → Monad M

  monad-return : {M : Set → Set} → Monad M → {T : Set} → T → M T
  monad-return (monad return bind) = return

  monad-bind : {M : Set → Set} → Monad M → {T U : Set} → M T → (T → M U) → M U
  monad-bind (monad return bind) = bind

module Monad {M : Set → Set} (m : Base.Monad M) where
  return : {T : Set} → T → M T
  return = Base.monad-return m

  _>>=_ : {T U : Set} → M T → (T → M U) → M U
  _>>=_ = Base.monad-bind m

  infixl 10 _>>=_

open Base
