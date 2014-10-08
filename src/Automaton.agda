module Automaton where

open import Data.List using (List)

String = List

data Language (Σ : Set) : Set₁ where
    language : (String Σ → Set) → Language Σ

{-
-- DFA ⇒ NFA
DFA⇒NFA : {Q Σ : Set} → DFA Q Σ → NFA Q Σ
DFA⇒NFA (dfa δ startState acceptStates) = nfa δ' startState acceptStates
    where   δ' : _ → _ → _
            δ' q (inj₁ x) = {!   !}
            δ' q (inj₂ ε) = {!   !}
-}
