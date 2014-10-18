module Automaton.NonDeterministic where

open import Automaton.Types using (String)

open import Data.Sum using (_⊎_)

-- ε, the "empty" character
data E : Set where
    ε : E

record NFA (Q : Set) (Σ : Set) : Set₁ where
    constructor nfa
    field
        δ : Q → (Σ ⊎ E) → (Q → Set)
        startState : Q
        acceptStates : Q → Set

run : {Q Σ : Set} → NFA Q Σ → Q → String Σ → Set
run m state string = {!   !}

accept : {Q Σ : Set} → NFA Q Σ → String Σ → Set
accept m string = run m (NFA.startState m) string
