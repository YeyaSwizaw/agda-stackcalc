module Result where

data Result (E T : Set) : Set where
  Err : E → Result E T
  Ok : T → Result E T

open import Monad

monad-result : (E : Set) → Base.Monad (Result E)
monad-result E = Base.monad return bind where
  return : {T : Set} → T → Result E T
  return x = Ok x

  bind : {T U : Set} → Result E T → (T → Result E U) → Result E U
  bind (Err e) _ = Err e
  bind (Ok x) f = f x

module MonadResult (E : Set) = Monad.Monad (monad-result E)
open MonadResult

{-
_>>=_ : {T U E : Set} → Result T E → (T → Result U E) → Result U E
Err e >>= f = Err e
Ok x >>= f = f x

_>>$_ : {T U E : Set} → Result T E → (T → U) → Result U E
Err e >>$ f = Err e
Ok x >>$ f = Ok (f x)
-}
