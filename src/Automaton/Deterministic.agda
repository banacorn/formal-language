module Automaton.Deterministic where

-- open import Automaton.Types using (String)

open import Data.Nat
open import Data.Bool
open import Data.Fin
open import Data.List
open import Data.Dist renaming (_∪_ to _∪D_; _∩_ to _∩D_)
open import Function

String = List ∘ Elem

record DFA (Q Σ : Structure) : Set where
    constructor dfa
    field
        δ : Elem Q → Elem Σ → Elem Q
        startState : Elem Q
        acceptState : Elem Q → Bool

open DFA

------------------------------------------------------------------------
-- Run & Accept

run : ∀ {Q Σ} → DFA Q Σ → Elem Q → String Σ → Bool
run automata state []       = acceptState automata state
run automata state (x ∷ xs) = run automata (δ automata state x) xs

accept : ∀ {Q Σ} → DFA Q Σ → String Σ → Bool
accept automata string = run automata (startState automata) string

------------------------------------------------------------------------
-- operations on DFA

-- Union
_∪_ : ∀ {Q₀ Q₁ Σ} → DFA Q₀ Σ → DFA Q₁ Σ → DFA (Q₀ ⨂ Q₁) Σ
_∪_ {Q₀} {Q₁} {Σ} (dfa δ₀ start₀ accept₀) (dfa δ₁ start₁ accept₁) =
    dfa δ₂ start₂ accept₂
    where   δ₂ : Elem (Q₀ ⨂ Q₁) → Elem Σ → Elem (Q₀ ⨂ Q₁)
            δ₂ (s₀ ⊗ s₁) a = δ₀ s₀ a ⊗ δ₁ s₁ a
            start₂ : Elem (Q₀ ⨂ Q₁)
            start₂ = start₀ ⊗ start₁
            accept₂ : Elem (Q₀ ⨂ Q₁) → Bool
            accept₂ (x ⊗ y) = accept₀ x ∨ accept₁ y

-- Intersection
_∩_ : ∀ {Q₀ Q₁ Σ} → DFA Q₀ Σ → DFA Q₁ Σ → DFA (Q₀ ⨂ Q₁) Σ
_∩_ {Q₀} {Q₁} {Σ} (dfa δ₀ start₀ accept₀) (dfa δ₁ start₁ accept₁) =
    dfa δ₂ start₂ accept₂
    where   δ₂ : Elem (Q₀ ⨂ Q₁) → Elem Σ → Elem (Q₀ ⨂ Q₁)
            δ₂ (s₀ ⊗ s₁) a = δ₀ s₀ a ⊗ δ₁ s₁ a
            start₂ : Elem (Q₀ ⨂ Q₁)
            start₂ = start₀ ⊗ start₁
            accept₂ : Elem (Q₀ ⨂ Q₁) → Bool
            accept₂ (x ⊗ y) = accept₀ x ∧ accept₁ y

-- Complement
¬_ : ∀ {Q Σ} → DFA Q Σ → DFA Q Σ
¬_ (dfa δ start accept) = dfa δ start (not ∘ accept)
