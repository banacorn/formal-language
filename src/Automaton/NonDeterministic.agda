module Automaton.NonDeterministic where

open import Automaton.Types using (String)

open import Data.Bool           using (true; false)
open import Data.Empty          using (⊥)
open import Data.Nat            using (ℕ; suc; zero; _+_)
open import Data.Fin            renaming (zero to Fzero)
open import Data.List           using (List; []; _∷_; foldr)
open import Data.Dist           using (FinSet; FinElem; Structure; ⨀; _⨁_; _⨂_;
                                    ⊙; ⊕₀; ⊕₁; _⊗_; insert; _∈-Bool_; _∈_; ⇒List)
import Relation.Unary           as RU

------------------------------------------------------------------------
-- NFA datatypes

-- ε, the "empty" character
E : Structure
E = ⨀ 1
ε : FinElem E
ε = ⊙ Fzero

record NFA (Q : Structure) (Σ : Structure) : Set where
    constructor nfa
    field
        δ : FinElem Q → FinElem (Σ ⨁ E) → FinSet Q
        startState : FinElem Q
        acceptStates : FinSet Q

open NFA

------------------------------------------------------------------------
-- Run & Accept

-- closure of Choices formed by collecting states reachable by ε
ε-closure : ∀ {Q Σ} → NFA Q Σ → FinElem Q → FinSet Q
ε-closure m state = insert state (δ m state (⊕₁ ε))

∪-fold : ∀ {A} → (P : A → Set) → List A → Set
∪-fold {A} P = foldr or ⊥
    where   or : A → Set → Set
            or x acc = (P RU.∪ λ _ → acc) x

run : ∀ {Q Σ} → NFA Q Σ → FinElem Q → String (FinElem Σ) → Set
run m state []       = state ∈ (acceptStates m)
run m state (x ∷ xs) = ∪-fold (λ s → run m s xs) (⇒List states')
    where   states' = ε-closure m state

accept : ∀ {Q Σ} → NFA Q Σ → String (FinElem Σ) → Set
accept m string = run m (startState m) string


------------------------------------------------------------------------
-- Opertations on NFA

-- Concatenation
_++_ : ∀ {Q₀ Q₁ Σ} → NFA Q₀ Σ → NFA Q₁ Σ → NFA (Q₀ ⨁ Q₁) Σ
_++_ {Q₀} {Q₁} {Σ} (nfa δ₀ start₀ accept₀) (nfa δ₁ start₁ accept₁) =
    nfa δ₂ (⊕₀ start₀) (⊕₁ accept₁)

    where   δ₂ : FinElem (Q₀ ⨁ Q₁) → FinElem (Σ ⨁ E) → FinSet (Q₀ ⨁ Q₁)
            δ₂ (⊕₀ state) a with state ∈-Bool accept₀
            δ₂ (⊕₀ state) a | true  = ⊕₁ (δ₁ start₁ a)
            δ₂ (⊕₀ state) a | false = ⊕₀ (δ₀ state  a)
            δ₂ (⊕₁ state) a         = ⊕₁ (δ₁ state  a)
