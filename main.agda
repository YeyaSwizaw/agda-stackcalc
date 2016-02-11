module Main where
open import Parse
open import Eval
open import Error
open import Result
open import Monad

open Result.MonadResult Error

test : EvalResult
test = parse "15 7 + () 5 * ()" >>= eval

