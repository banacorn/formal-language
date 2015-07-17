module Automaton.Deterministic where

-- open import Automaton.Types using (String)

open import Data.Nat
open import Data.Fin
open import Data.Fin.Subset
open import Data.List

String = List

record DFA (Q Σ : ℕ) : Set where
    constructor dfa
    field
        δ : Fin Q → Fin Σ → Fin Q
        startState : Fin Q
        acceptState : Subset Q

open DFA

------------------------------------------------------------------------
-- Run & Accept

run : ∀ {Q Σ} → DFA Q Σ → Fin Q → String (Fin Σ) → Set
run automata state []       = state ∈ acceptState automata
run automata state (x ∷ xs) = run automata (δ automata state x) xs

accept : ∀ {Q Σ} → DFA Q Σ → String (Fin Σ) → Set
accept automata string = run automata (startState automata) string

------------------------------------------------------------------------
-- operations on DFA

-- Union
-- _∪_ : ∀ {Q₀ Q₁ Σ} → DFA Q₀ Σ → DFA Q₁ Σ → DFA (Q₀ ⨂ Q₁) Σ



-- _∪_ {Q₀} {Q₁} {Σ} (dfa δ₀ start₀ accept₀) (dfa δ₁ start₁ accept₁) =
--     dfa δ₂ start₂ accept₂
--     where   δ₂ : FinElem (Q₀ ⨂ Q₁) → FinElem Σ → FinElem (Q₀ ⨂ Q₁)
--             δ₂ (s₀ ⊗ s₁) a = δ₀ s₀ a ⊗ δ₁ s₁ a
--             start₂ : FinElem (Q₀ ⨂ Q₁)
--             start₂ = start₀ ⊗ start₁
--             accept₂ : FinSet (Q₀ ⨂ Q₁)
--             accept₂ = {!   !}
--
-- -- Intersection
-- _∩_ : ∀ {Q₀ Q₁ Σ} → DFA Q₀ Σ → DFA Q₁ Σ → DFA (Q₀ ⨂ Q₁) Σ
-- _∩_ {Q₀} {Q₁} {Σ} (dfa δ₀ start₀ accept₀) (dfa δ₁ start₁ accept₁) =
--     dfa δ₂ start₂ accept₂
--     where   δ₂ : FinElem (Q₀ ⨂ Q₁) → FinElem Σ → FinElem (Q₀ ⨂ Q₁)
--             δ₂ (s₀ ⊗ s₁) a = δ₀ s₀ a ⊗ δ₁ s₁ a
--             start₂ : FinElem (Q₀ ⨂ Q₁)
--             start₂ = start₀ ⊗ start₁
--             accept₂ : FinSet (Q₀ ⨂ Q₁)
--             accept₂ = accept₀ ⊗ accept₁
--
-- -- Complement
-- ¬_ : ∀ {Q Σ} → DFA Q Σ → DFA Q Σ
-- ¬_ (dfa δ start accept) = dfa δ start (∁ accept)
