module Automaton.NonDeterministic where

open import Automaton.Types using (String)

open import Data.Bool           using (true; false)
open import Data.Nat            using (ℕ; suc; zero; _+_)
open import Data.Fin            using (Fin)
                                renaming (zero to Fzero; suc to Fsuc)
open import Dist                using (FinSet; FinElem; Structure; ⨀; _⨁_; _⨂_;
                                    ⊙; ⊕₀; ⊕₁; _⊗_; insert; _∈-Bool_)

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

-- closure of Choices formed by collecting states reachable by ε
ε-closure : ∀ {Q Σ} → NFA Q Σ → FinElem Q → FinSet Q
ε-closure m state = insert state (δ m state (⊕₁ ε))

{-
toBool : Set → Bool
toBool ⊤ = true

run' : ∀ {q σ} → NFA q σ → Q q → String (Σ σ) → Bool
run' m state [] = toBool (state ∈ acceptStates m)
run' {q} m state (x ∷ xs) = or (⇒List states' >>= map runWithState ∘ ⇒List ∘ transitWithState)
    where   states' = ε-closure m state

            runWithState : Q q → Bool
            runWithState q = run' m q xs

            transitWithState : Q q → Subset q
            transitWithState q = δ m q (Data.Sum.inj₁ x)

run : ∀ {q σ} → NFA q σ → Q q → String (Σ σ) → Set
run m state = T ∘ run' m state

accept : ∀ {q σ} → NFA q σ → String (Σ σ) → Set
accept m string = run m (startState m) string
-}

-- concatenation
_++_ : ∀ {Q₀ Q₁ Σ} → NFA Q₀ Σ → NFA Q₁ Σ → NFA (Q₀ ⨁ Q₁) Σ
_++_ {Q₀} {Q₁} {Σ} (nfa δ₀ start₀ accept₀) (nfa δ₁ start₁ accept₁) =
    nfa δ₂ (⊕₀ start₀) (⊕₁ accept₁)

    where   δ₂ : FinElem (Q₀ ⨁ Q₁) → FinElem (Σ ⨁ E) → FinSet (Q₀ ⨁ Q₁)
            δ₂ (⊕₀ state) a with state ∈-Bool accept₀
            δ₂ (⊕₀ state) a | true  = ⊕₁ (δ₁ start₁ a)
            δ₂ (⊕₀ state) a | false = ⊕₀ (δ₀ state  a)
            δ₂ (⊕₁ state) a         = ⊕₁ (δ₁ state  a)
