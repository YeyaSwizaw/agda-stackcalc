module List where

data List (T : Set) : Set where
  [] : List T
  _∷_ : T → List T → List T

infixr 3 _∷_

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _∷_ #-}

[_] : {T : Set} → T → List T
[ x ] = x ∷ []
