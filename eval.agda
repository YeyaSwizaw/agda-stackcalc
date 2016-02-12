module Eval where
open import Instr
open import Nat
open import Char
open import List
open import Result
open import Error
open import Equality

open Result.MonadResult Error

EvalResult : Set
EvalResult = Result Error (List Value)

apply-op : (n : ℕ) → Operator n → List Value → EvalResult
apply-op 2 op (Val x ∷ Val y ∷ stack) = Ok (Val (Int ((op-fn 2 op) (as-nat x) (as-nat y))) ∷ stack)
apply-op n op stack = Err (ApplicationError op)

run-eval : List Instr → List Value → EvalResult
run-eval [] stack = Ok stack
run-eval (Push x ∷ instrs) stack = run-eval instrs (x ∷ stack)
run-eval (Pop ∷ instrs) [] = Err EmptyPop
run-eval (Pop ∷ instrs) (x ∷ stack) = run-eval instrs stack
run-eval (Apply ∷ instrs) (Op n op ∷ stack) = apply-op n op stack >>= run-eval instrs
run-eval (Apply ∷ instrs) stack = Err EmptyApply

eval : List Instr → EvalResult
eval instrs = run-eval instrs []

-- Proofs
push-value : ∀ (v : Value) → eval [ Push v ] ≡ Ok [ v ]
push-value _ = refl

push-pop : ∀ (v : Value) → eval (Push v ∷ Pop ∷ []) ≡ Ok []
push-pop _ = refl

pop-empty : eval [ Pop ] ≡ Err EmptyPop
pop-empty = refl

apply-add : ∀ (x y : Operatable) → eval (Push (Val y) ∷ Push (Val x) ∷ Push (Op 2 Plus) ∷ Apply ∷ []) ≡ Ok [ Val (Int (as-nat x + as-nat y)) ]
apply-add _ _ = refl
