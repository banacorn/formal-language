-- open import Nat
open import Data.List using (List; []; _∷_)

record DFA (Q : Set) (Σ : Set) : Set₁ where
    constructor dfa
    field
        δ : Q -> Σ -> Q
        startState : Q
        acceptStates : Q -> Set

String = List

run : {Q Σ : Set} -> DFA Q Σ -> Q -> String Σ -> Set
run M s (w0 ∷ w) = run M ((DFA.δ M) s w0) w
run M s [] = DFA.acceptStates M s

accept : {Q Σ : Set} -> DFA Q Σ -> String Σ -> Set
accept M S = run M (DFA.startState M) S
