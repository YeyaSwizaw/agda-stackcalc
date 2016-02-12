module Main where
open import String
open import Parse
open import Eval
open import Error
open import Instr
open import List
open import Result
open import Monad
open import IO

test : String
test = "15 7 + () 5 * ()"

module IOM = MonadIO
module ResM = MonadResult Error

print : EvalResult → IO Unit
print (Err x) = IOM.return unit
print (Ok []) = IOM.return unit
print (Ok (Val (Char x) ∷ xs)) = putStr (showChar x) IOM.>>= λ _ → putStr " " IOM.>>= λ _ → print (Ok xs)
print (Ok (Val (Int x) ∷ xs)) = putStr (showNat x) IOM.>>= λ _ → putStr " " IOM.>>= λ _ → print (Ok xs)
print (Ok (Op .2 Plus ∷ xs)) = putStr "+ " IOM.>>= λ _ → print (Ok xs)
print (Ok (Op .2 Mul ∷ xs)) = putStr "* " IOM.>>= λ _ → print (Ok xs)

main = run (
    putStr "Enter Calculation: " IOM.>>= λ _ → 
    getLine IOM.>>= λ input →
    print (parse input ResM.>>= eval) IOM.>>= λ _ →
    putStrLn "")
