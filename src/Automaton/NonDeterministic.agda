module Automaton.NonDeterministic where

open import Automaton.Types using (String)

open import Data.Empty          using (⊥)
open import Data.Bool           using (Bool)
open import Category.Monad      using (RawMonad; module RawMonad)
open import Data.List           using (List; []; _∷_; foldr; monad; map; concat)
open RawMonad {_} monad         using (return; _>>=_)
open import Data.Vec            using (Vec)
                                renaming ([] to []v; _∷_ to _∷v_)
open import Data.Nat            using (ℕ; suc; zero)
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

run : ∀ {q σ} → NFA q σ → Q q → String (Σ σ) → Set
run m state [] = state ∈ acceptStates m
run m state (x ∷ xs) = foldr {!   !} {!   !} (map (λ q → const (run m q xs)) (⇒List states' >>= (λ q → ⇒List (δ m q (Data.Sum.inj₁ x)) ) ))
    where   states' = ε-closure m state




-- accept : {Q Σ : Set} → NFA Q Σ → String Σ → Set
-- accept m string = run m (startState m) string
