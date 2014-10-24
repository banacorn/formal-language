module Automaton.NonDeterministic where

open import Automaton.Types using (String)

open import Data.Empty          using (⊥)
open import Data.Bool           using (Bool; true; false; T)
open import Category.Monad      using (RawMonad; module RawMonad)
open import Data.List           using (List; []; _∷_; foldr; monad; map; concat; or)
open import Level using (zero)
open RawMonad {zero} monad             using (return; _>>=_)
open import Data.Nat            using (ℕ; suc; zero; _+_)
open import Data.Vec            using (Vec)
                                renaming ([] to []v; _∷_ to _∷v_)
open import Data.Fin            using (Fin; compare; less; equal; greater; fromℕ; inject+)
open import Data.Fin.Subset     using (Subset; ⁅_⁆; _∈_; _∪_)
open import Data.Sum            using (_⊎_; inj₁; inj₂)
open import Data.Unit           using (⊤)
open import Function            using (_∘_; const)
import Relation.Unary           as RU
open import Util                using (⇒List; inj[_+_]_; inj₁Subset; inj₂Subset)



-- ε, the "empty" character
data E : Set where
    ε : E

-- Finite State & Alphabet
Q = Fin
Σ = Fin

record NFA (q : ℕ) (σ : ℕ) : Set₁ where
    constructor nfa
    field
        δ : Q q → (Σ σ ⊎ E) → Subset q
        startState : Q q
        acceptStates : Subset q

open NFA

-- closure of Choices formed by collecting states reachable by ε
ε-closure : ∀ {q σ} → NFA q σ → Q q → Subset q
ε-closure m state = ⁅ state ⁆ ∪ δ m state (Data.Sum.inj₂ ε)

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
            δ₂ q a with inj[ q₀ + q₁ ] q
            δ₂ q a | inj₁ state₀ = inj₁Subset (δ₀ state₀ a)
            δ₂ q a | inj₂ state₁ = inj₂Subset (δ₁ state₁ a)
