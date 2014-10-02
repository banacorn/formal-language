-- open import Nat
open import Data.List using (List; []; _∷_)

data Subset (A : Set) : Set₁ where
    ∈ : ((a : A) -> Set) -> Subset A

record DFA (Q : Set)  (Σ : Set) : Set₁ where
    constructor DFA[_,_,_]
    field
        δ : Q -> Σ -> Q
        startState : Q
        acceptStates : Subset Q

String = List

run : {Q Σ : Set} -> DFA Q Σ -> Q -> String Σ -> Set
run M s (w0 ∷ w) = run M ((DFA.δ M) s w0) w
run M s [] with DFA.acceptStates M
run M s [] | ∈ f = f s

-- a language is regular iff some DFA recognizes it
Regular : {Q Σ : Set} -> DFA Q Σ -> String Σ -> Set
Regular M S = run M (DFA.startState M) S
