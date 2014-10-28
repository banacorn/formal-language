module Automaton.Deterministic where

open import Automaton.Types using (String)

open import Data.List           using (List; _∷_; [])
open import Dist                using (FinSet; FinElem; Structure; ⨀; _⨁_; _⨂_;
                                    ⊙; ⊕₀; ⊕₁; _⊗_; _∈_)

record DFA (Q : Structure) (Σ : Structure) : Set where
    constructor dfa
    field
        δ : FinElem Q → FinElem Σ → FinElem Q
        startState : FinElem Q
        acceptStates : FinSet Q

open DFA

------------------------------------------------------------------------
-- Run & Accept

run : ∀ {Q Σ} → DFA Q Σ → FinElem Q → String (FinElem Σ) → Set
run m state (x ∷ xs) = run m (δ m state x) xs
run m state []       = state ∈ acceptStates m

accept : ∀ {Q Σ} → DFA Q Σ → String (FinElem Σ) → Set
accept m state = run m (startState m) state


-- union
_∪_ : ∀ {Q₀ Q₁ Σ} → DFA Q₀ Σ → DFA Q₁ Σ → DFA (Q₀ ⨂ Q₁) Σ
_∪_ {Q₀} {Q₁} {Σ} (dfa δ₀ start₀ accept₀) (dfa δ₁ start₁ accept₁) =
    dfa δ₂ start₂ accept₂
    where   δ₂ : FinElem (Q₀ ⨂ Q₁) → FinElem Σ → FinElem (Q₀ ⨂ Q₁)
            δ₂ (s₀ ⊗ s₁) a = δ₀ s₀ a ⊗ δ₁ s₁ a
            start₂ : FinElem (Q₀ ⨂ Q₁)
            start₂ = start₀ ⊗ start₁
            accept₂ : FinSet (Q₀ ⨂ Q₁)
            accept₂ = accept₀ ⊗ accept₁

{-}
_∪_ {Q₀} {Q₁} {Σ} (dfa δ₀ start₀ accept₀) (dfa δ₁ start₁ accept₁) =
    dfa δ₂ start₂ accept₂
    where   δ₂      = λ {(q₀ , q₁) a → δ₀ q₀ a , δ₁ q₁ a}
            start₂  = start₀ , start₁
            accept₂ = accept₀ Function.∘ proj₁ Relation.Unary.∪ accept₁ Function.∘ proj₂


-- intersection
_∩_ : {Q₀ Q₁ Σ : Set} → DFA Q₀ Σ → DFA Q₁ Σ → DFA (Q₀ × Q₁) Σ
_∩_ {Q₀} {Q₁} {Σ} (dfa δ₀ start₀ accept₀) (dfa δ₁ start₁ accept₁) =
    dfa δ₂ start₂ accept₂
    where   δ₂      = λ {(q₀ , q₁) a → δ₀ q₀ a , δ₁ q₁ a}
            start₂  = start₀ , start₁
            accept₂ = accept₀ Function.∘ proj₁ Relation.Unary.∩ accept₁ Function.∘ proj₂

-- complement
¬ : {Q Σ : Set} → DFA Q Σ → DFA Q Σ
¬ (dfa δ start accept) = dfa δ start (Relation.Unary.∁ accept)

-}
