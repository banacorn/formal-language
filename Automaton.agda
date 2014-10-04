module Automaton where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Relation.Unary using (_∪_)
open import Function using (_∘_)

record DFA (Q : Set) (Σ : Set) : Set₁ where
    constructor dfa
    field
        δ : Q → Σ → Q
        startState : Q
        acceptStates : Q → Set

String = List

run : {Q Σ : Set} → DFA Q Σ → Q → String Σ → Set
run M s (w0 ∷ w) = run M ((DFA.δ M) s w0) w
run M s [] = DFA.acceptStates M s

accept : {Q Σ : Set} → DFA Q Σ → String Σ → Set
accept M S = run M (DFA.startState M) S


-- union
_∪_ : {Q₀ Q₁ Σ : Set} → DFA Q₀ Σ → DFA Q₁ Σ → DFA (Q₀ × Q₁) Σ
_∪_ {Q₀} {Q₁} {Σ} (dfa δ₀ start₀ accept₀) (dfa δ₁ start₁ accept₁) =
    dfa δ₂ start₂ accept₂
    where   δ₂      = λ {(q₀ , q₁) a → δ₀ q₀ a , δ₁ q₁ a}
            start₂  = start₀ , start₁
            accept₂ = accept₀ ∘ proj₁ Relation.Unary.∪ accept₁ ∘ proj₂

-- definition of Language
data Language (Σ : Set) : Set₁ where
    language : (String Σ → Set) → Language Σ
