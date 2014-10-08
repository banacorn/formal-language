module Automaton where

open import Automaton.Deterministic using (DFA; dfa)
open import Automaton.NonDeterministic using (NFA; nfa)

open import Data.Sum using (inj₁; inj₂)

{-
-- DFA ⇒ NFA
DFA⇒NFA : {Q Σ : Set} → DFA Q Σ → NFA Q Σ
DFA⇒NFA (dfa δ startState acceptStates) = nfa δ' startState acceptStates
    where   δ' : _ → _ → _
            δ' q (inj₁ x) = {!   !}
            δ' q (inj₂ ε) = {!   !}
-}
