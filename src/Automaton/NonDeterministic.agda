module Automaton.NonDeterministic where

open import Automaton.Types using (String)

open import Data.Nat            using (ℕ; suc; zero; _+_)
open import Data.Fin            using (Fin)
                                renaming (zero to Fzero; suc to Fsuc)
open import Dist                using (FinSet; FinElem; Structure; ⨀; _⨁_; _⨂_; ⊙; ⊕₀; ⊕₁; _⊗_; insert)

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

-- concatenation
_++_ : ∀ {q₀ q₁ σ} → NFA q₀ σ → NFA q₁ σ → NFA (q₀ + q₁) σ
_++_ {q₀} {q₁} {σ} (nfa δ₀ start₀ accept₀) (nfa δ₁ start₁ accept₁) = nfa δ₂ (inject+ q₁ start₀) (inj₂Subset accept₁)

    where   δ₂ : Q (q₀ + q₁) → (Σ σ ⊎ E) → Subset (q₀ + q₁)
            δ₂ q a with proj[ q₀ + q₁ ] q
            δ₂ q a | inj₂ state₁ = inj₂Subset (δ₁ state₁ a)
            δ₂ q a | inj₁ state₀ with state₀ ∈-Bool accept₀
            δ₂ q a | inj₁ state₀ | true = inj₂Subset (δ₁ start₁ a)
            δ₂ q a | inj₁ state₀ | false = inj₁Subset (δ₀ state₀ a)
-}
