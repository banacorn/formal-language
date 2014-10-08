module Automaton.NonDeterministic where

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
