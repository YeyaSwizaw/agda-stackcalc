module Monad where
open import Agda.Primitive

module Base where
  data Monad {n : Level} (M : Set → Set n) : Set (lsuc n) where
    monad : (return : {T : Set} → T → M T) → (bind : {T U : Set} → M T → (T → M U) → M U) → Monad M

  monad-return : {n : Level} → {M : Set → Set n} → Monad M → {T : Set} → T → M T
  monad-return (monad return bind) = return

  monad-bind : {n : Level} → {M : Set → Set n} → Monad M → {T U : Set} → M T → (T → M U) → M U
  monad-bind (monad return bind) = bind

module Monad {n} {M : Set → Set n} (m : Base.Monad M) where
  return : {T : Set} → T → M T
  return = Base.monad-return m

  _>>=_ : {T U : Set} → M T → (T → M U) → M U
  _>>=_ = Base.monad-bind m

  infixl 10 _>>=_

open Base
