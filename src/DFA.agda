module DFA where

open import Data.Bool using (Bool)

-- A deterministic finite automaton is a 5-tuple, (Q, Σ, δ, q0, F)
record DFA (Q Σ : Set) : Set where
    field
        δ : Q → Σ → Q
        initial : Q
        accept : Q → Bool

-- run : 
