module Automaton.Types where

open import Data.List using (List)

String = List

data Language (Σ : Set) : Set₁ where
    language : (String Σ → Set) → Language Σ
