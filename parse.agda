module Parse where
open import Instr
open import String
open import Nat
open import Char
open import List
open import Result
open import Error
open import Equality

open Result.MonadResult Error

_◦_ : {T U V : Set} → (T → U) → (U → V) → (T → V)
f ◦ g = λ x → g (f x)

ParseResult : Set
ParseResult = Result Error (List Instr)

parse-run : List Character -> List Instr → ParseResult
parse-int : ℕ → List Character → List Instr → ParseResult
parse-apply : List Character → List Instr → ParseResult

parse-run [] instrs = Ok instrs
parse-run (' ' ∷ input) instrs = parse-run input instrs

parse-run ('(' ∷ input) instrs = parse-apply input instrs

parse-run ('+' ∷ input) instrs = parse-run input instrs >>= _∷_ (Push (Op 2 Plus)) ◦ return
parse-run ('*' ∷ input) instrs = parse-run input instrs >>= _∷_ (Push (Op 2 Mul)) ◦ return

parse-run ('0' ∷ input) instrs = parse-int 0 input instrs
parse-run ('1' ∷ input) instrs = parse-int 1 input instrs
parse-run ('2' ∷ input) instrs = parse-int 2 input instrs
parse-run ('3' ∷ input) instrs = parse-int 3 input instrs
parse-run ('4' ∷ input) instrs = parse-int 4 input instrs
parse-run ('5' ∷ input) instrs = parse-int 5 input instrs
parse-run ('6' ∷ input) instrs = parse-int 6 input instrs
parse-run ('7' ∷ input) instrs = parse-int 7 input instrs
parse-run ('8' ∷ input) instrs = parse-int 8 input instrs
parse-run ('9' ∷ input) instrs = parse-int 9 input instrs

parse-run (c ∷ input) instrs = Err (UnexpectedChar c)

parse-int n [] instrs = Ok (Push (Val (Int n)) ∷ instrs)
parse-int n ('0' ∷ input) instrs = parse-int (n * 10) input instrs
parse-int n ('1' ∷ input) instrs = parse-int ((n * 10) + 1) input instrs
parse-int n ('2' ∷ input) instrs = parse-int ((n * 10) + 2) input instrs
parse-int n ('3' ∷ input) instrs = parse-int ((n * 10) + 3) input instrs
parse-int n ('4' ∷ input) instrs = parse-int ((n * 10) + 4) input instrs
parse-int n ('5' ∷ input) instrs = parse-int ((n * 10) + 5) input instrs
parse-int n ('6' ∷ input) instrs = parse-int ((n * 10) + 6) input instrs
parse-int n ('7' ∷ input) instrs = parse-int ((n * 10) + 7) input instrs
parse-int n ('8' ∷ input) instrs = parse-int ((n * 10) + 8) input instrs
parse-int n ('9' ∷ input) instrs = parse-int ((n * 10) + 9) input instrs
parse-int n (x ∷ input) instrs = parse-run (x ∷ input) instrs >>= _∷_ (Push (Val (Int n))) ◦ return

parse-apply [] instrs = Err (ExpectedChar ')' ' ')
parse-apply (')' ∷ input) instrs = parse-run input instrs >>= _∷_ Apply ◦ return
parse-apply (c ∷ input) instrs = Err (ExpectedChar ')' 'c')

parse : String → ParseResult
parse input = parse-run (primStringToList input) []
