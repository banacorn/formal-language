module Automaton.Deterministic where

open import Automaton.Types using (String)


open import Data.Nat            using (ℕ; suc; zero; _+_; _*_)
open import Data.Fin            using (Fin)
open import Data.Fin.Subset     using (Subset; _∈_)
open import Data.List           using ([]; _∷_)
open import Data.Product        using (_×_; _,_; proj₁; proj₂)
import Relation.Unary           as RU
-- open import Relation.Unary      using (_∈_)
import Relation.Unary           using (_∪_; _∩_; ∁)
import Function                 using (_∘_)

-- Finite State & Alphabet
Q = Fin
Σ = Fin

record DFA (q : ℕ) (σ : ℕ) : Set where
    constructor dfa
    field
        δ : Q q → Σ σ → Q q
        startState : Q q
        acceptStates : Subset q

open DFA

-- run & accept
run : ∀ {q σ} → DFA q σ → Q q → String (Σ σ) → Set
run m state (x ∷ xs) = run m (δ m state x) xs
run m state [] = state ∈ (acceptStates m)


accept : ∀ {q σ} → DFA q σ → String (Σ σ) → Set
accept m state = run m (startState m) state
{-
-- union
_∪_ : ∀ {q₀ q₁ σ} → DFA q₀ σ → DFA q₁ σ → DFA (q₀ * q₁) σ
_∪_ {q₀ q₁} {σ} (dfa δ₀ start₀ accept₀) (dfa δ₁ start₁ accept₁) = {!   !}


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
