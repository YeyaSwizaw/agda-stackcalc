module Main where
open import String
open import Parse
open import Eval
open import Error
open import Instr
open import List
open import Result
open import IO

test : String
test = "15 7 + () 5 * ()"

module IOM = MonadIO
module ResM = MonadResult Error

put-space : {T : Set} → T → IO Unit
put-space _ = putStr " "

put-str : {T : Set} → String → T → IO Unit
put-str str _ = putStr str

print : EvalResult → IO Unit
print (Err err) = putStr (showErr err)
print (Ok []) = IOM.return unit
print (Ok (Val (Char x) ∷ xs)) = print (Ok xs) IOM.>>= put-str (showChar x) IOM.>>= put-space
print (Ok (Val (Int x) ∷ xs)) = print (Ok xs) IOM.>>= put-str (showNat x) IOM.>>= put-space
print (Ok (Op _ op ∷ xs)) = print (Ok xs) IOM.>>= put-str (showOp op) IOM.>>= put-space

{-# NON_TERMINATING #-}
read-input : List Value → IO Unit
handle-input : List Value → String → IO Unit
handle-result : List Value → EvalResult → IO Unit

read-input stack = 
  putStr ">>= " IOM.>>= λ _ →
  getLine IOM.>>= handle-input stack

handle-input _ "quit" = IOM.return unit
handle-input _ "exit" = IOM.return unit

handle-input stack input = 
  handle-result stack (
    parse input ResM.>>= λ instrs → 
    run-eval instrs stack)

handle-result stack (Err err) = 
  print (Err err) IOM.>>= λ _ →
  putStrLn "" IOM.>>= λ _ →
  read-input stack

handle-result _ (Ok stack) =
  print (Ok stack) IOM.>>= λ _ →
  read-input stack

main = run (read-input [])
