module IO where
open import String

module Primitive where
  data Unit : Set where
    unit : Unit

  {-# COMPILED_DATA Unit () () #-}

  postulate
    IO : ∀ {a} → Set a → Set a

  {-# IMPORT IO.FFI #-}
  {-# COMPILED_TYPE IO IO.FFI.AgdaIO #-}
  {-# BUILTIN IO IO #-}

  postulate
    return : {T : Set} → T → IO T
    _>>=_ : {T : Set} {U : Set} → IO T → (T → IO U) → IO U

  {-# COMPILED return (\_ -> return) #-}
  {-# COMPILED _>>=_  (\_ _ -> (>>=)) #-}

  {-# IMPORT Data.Text.IO #-}

  postulate
    putStr : String → IO Unit
    putStrLn : String → IO Unit

  {-# COMPILED putStr putStr #-}
  {-# COMPILED putStrLn putStrLn #-}

data IO (T : Set) : Set₁ where
  lift : Primitive.IO T → IO T
  ret : T → IO T
  bind : {U : Set} → IO U → (U → IO T) → IO T

open import Monad

monad-io : Base.Monad IO
monad-io = Base.monad ret bind where

module MonadIO = Monad.Monad monad-io
open MonadIO

{-# NON_TERMINATING #-}

run : {T : Set} → IO T → Primitive.IO T
run (lift m) = m
run (ret x) = Primitive.return x
run (bind m f) = run m Primitive.>>= (λ x → run (f x))

data Unit : Set where
  unit : Unit

putStr : String → IO Unit
putStr s = lift (Primitive.putStr s) >>= λ _ → return unit

putStrLn : String → IO Unit
putStrLn s = lift (Primitive.putStrLn s) >>= λ _ → return unit
