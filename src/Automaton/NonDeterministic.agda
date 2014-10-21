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
open import Data.Fin            using (Fin)
open import Data.Sum            using (_⊎_)
open import Data.Unit           using (⊤)
open import Function            using (_∘_; const)
import Relation.Unary           as RU
open import FinSet              using (FinSet; _∈_; _∪_; embed; singleton; ⇒List)


-- ε, the "empty" character
data E : Set where
    ε : E

-- Finite State & Alphabet
Q = Fin
Σ = Fin

record NFA (q : ℕ) (σ : ℕ) : Set₁ where
    constructor nfa
    field
        δ : Q q → (Σ σ ⊎ E) → FinSet q
        startState : Q q
        acceptStates : FinSet q

open NFA

-- closure of Choices formed by collecting states reachable by ε
ε-closure : ∀ {q σ} → NFA q σ → Q q → FinSet q
ε-closure m state = singleton state ∪ δ m state (Data.Sum.inj₂ ε)

toBool : Set → Bool
toBool ⊤ = true


run' : ∀ {q σ} → NFA q σ → Q q → String (Σ σ) → Bool
run' m state [] = toBool (state ∈ acceptStates m)
run' {q} m state (x ∷ xs) = or (⇒List states' >>= map runWithState ∘ ⇒List ∘ transitWithState)
    where   states' = ε-closure m state

            runWithState : Q q → Bool
            runWithState q = run' m q xs

            transitWithState : Q q → FinSet q
            transitWithState q = δ m q (Data.Sum.inj₁ x)

run : ∀ {q σ} → NFA q σ → Q q → String (Σ σ) → Set
run m state = T ∘ run' m state

accept : ∀ {q σ} → NFA q σ → String (Σ σ) → Set
accept m string = run m (startState m) string


-- concatenation
_++_ : ∀ {q₀ q₁ σ} → NFA q₀ σ → NFA q₁ σ → NFA (q₀ + q₁) σ
_++_ {q₀} {q₁} {σ} (nfa δ₀ start₀ accept₀) (nfa δ₁ start₁ accept₁) = {! nfa δ₂  !}
    where   δ₂ : Q (q₀ + q₁) → (Σ σ ⊎ E) → FinSet (q₀ + q₁)
            δ₂ q a = {! q  !}
