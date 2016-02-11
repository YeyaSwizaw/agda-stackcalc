module Option where

data Option (T : Set) : Set where
  None : Option T
  Some : T → Option T

_?? : Set → Set
t ?? = Option t

infixl 3 _??

open import Monad

monad-option : Base.Monad Option
monad-option = Base.monad return bind where
  return : {T : Set} → T → Option T
  return x = Some x

  bind : {T U : Set} → Option T → (T → Option U) → Option U
  bind None _ = None
  bind (Some x) f = f x

module MonadOption = Monad.Monad monad-option
open MonadOption
