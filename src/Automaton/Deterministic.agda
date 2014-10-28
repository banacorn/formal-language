module Automaton.Deterministic where

open import Automaton.Types using (String)

open import Dist

record DFA (Q : Structure) (Σ : Structure) : Set where
    constructor dfa
    field
        δ : FinElem Q → FinElem Σ → FinElem Q
        startState : FinElem Q
        acceptStates : FinSet Q

open DFA

{-
-- run & accept
run : ∀ {q σ} → DFA q σ → Q q → String (Σ σ) → Set
run m state (x ∷ xs) = run m (δ m state x) xs
run m state [] = state ∈ (acceptStates m)


accept : ∀ {q σ} → DFA q σ → String (Σ σ) → Set
accept m state = run m (startState m) state

-- union
_∪_ : ∀ {q₀ q₁ σ} → DFA q₀ σ → DFA q₁ σ → DFA (q₀ * q₁) σ
_∪_ {q₀} {q₁} {σ} (dfa δ₀ start₀ accept₀) (dfa δ₁ start₁ accept₁) =
    dfa δ₂ start₂ accept₂
    where
            δ₂      : Q (q₀ * q₁) → Σ σ → Q (q₀ * q₁)
            δ₂ state a with proj[ q₀ * q₁ ] state
            ... | (m, n) = {!   !}
            start₂  = {! start₀ , start₁  !}
            accept₂ = {!   !}


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
