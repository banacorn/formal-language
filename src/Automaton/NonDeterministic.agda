module Automaton.NonDeterministic where

open import Automaton.Types using (String)

open import Data.Empty        using (⊥)
open import Data.List       using ([]; _∷_)
open import Data.Sum        using (_⊎_)
open import Data.Unit        using (⊤)
open import Relation.Unary  using (_∈_)
import Relation.Unary       as RU

-- ε, the "empty" character
data E : Set where
    ε : E

record NFA (Q : Set) (Σ : Set) : Set₁ where
    constructor nfa
    field
        δ : Q → (Σ ⊎ E) → (Q → Set)
        startState : Q
        acceptStates : Q → Set

open NFA

run : {Q Σ : Set} → NFA Q Σ → Q → String Σ → Set
run m state [] = state ∈ acceptStates m
run m state (x ∷ xs) = {!   !}

ε-closure : ∀ {Q Σ} → NFA Q Σ → Q → (Q → Set)
ε-closure m state = self RU.∪ reached-by-ε
    where   self = λ { state → ⊤ }
            reached-by-ε = δ m state (Data.Sum.inj₂ ε)

accept : {Q Σ : Set} → NFA Q Σ → String Σ → Set
accept m string = run m (startState m) string
