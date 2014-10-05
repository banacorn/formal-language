module Automaton where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Unary using (_∪_; _∩_; ∁)
open import Relation.Unary using (_∈_)
import Function using (_∘_)

record DFA (Q : Set) (Σ : Set) : Set₁ where
    constructor dfa
    field
        δ : Q → Σ → Q
        startState : Q
        acceptStates : Q → Set

-- ε, the "empty" character
data E : Set where
    ε : E

record NFA (Q : Set) (Σ : Set) : Set₁ where
    constructor nfa
    field
        δ : Q → (Σ ⊎ E) → (Q → Set)
        startState : Q
        acceptStates : Q → Set

-- String & Language
String = List

data Language (Σ : Set) : Set₁ where
    language : (String Σ → Set) → Language Σ

-- run & accept
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
            accept₂ = accept₀ Function.∘ proj₁ Relation.Unary.∪ accept₁ Function.∘ proj₂

∪⇒ : {Q₀ Q₁ Σ : Set} {s : String Σ} {a : DFA Q₀ Σ} {b : DFA Q₁ Σ}
    → (accept a Relation.Unary.∪ accept b) s
    → accept (a ∪ b) s
∪⇒ {s = []}     ∪∘accept  = ∪∘accept
∪⇒ {s = x ∷ xs} (inj₁ x₁) = ∪⇒ (inj₁ ∪⇒)
∪⇒ {s = x ∷ xs} (inj₂ x₂) = ∪⇒ (inj₂ ∪⇒)

∪⇐ : {Q₀ Q₁ Σ : Set} {s : String Σ} {a : DFA Q₀ Σ} {b : DFA Q₁ Σ}
    → accept (a ∪ b) s
    → (accept a Relation.Unary.∪ accept b) s
∪⇐ {s = []}     accept∘∪ = accept∘∪
∪⇐ {s = x ∷ xs} accept∘∪ = ∪⇐ accept∘∪

-- intersection
_∩_ : {Q₀ Q₁ Σ : Set} → DFA Q₀ Σ → DFA Q₁ Σ → DFA (Q₀ × Q₁) Σ
_∩_ {Q₀} {Q₁} {Σ} (dfa δ₀ start₀ accept₀) (dfa δ₁ start₁ accept₁) =
    dfa δ₂ start₂ accept₂
    where   δ₂      = λ {(q₀ , q₁) a → δ₀ q₀ a , δ₁ q₁ a}
            start₂  = start₀ , start₁
            accept₂ = accept₀ Function.∘ proj₁ Relation.Unary.∩ accept₁ Function.∘ proj₂

∩⇒ : {Q₀ Q₁ Σ : Set} {s : String Σ} {a : DFA Q₀ Σ} {b : DFA Q₁ Σ}
    → (accept a Relation.Unary.∩ accept b) s
    → accept (a ∩ b) s
∩⇒ {s = []}     ∩∘accept  = ∩∘accept
∩⇒ {s = x ∷ xs} (proj₁ , proj₂) = ∩⇒ (∩⇒ , ∩⇒)

∩⇐ : {Q₀ Q₁ Σ : Set} {s : String Σ} {a : DFA Q₀ Σ} {b : DFA Q₁ Σ}
    → accept (a ∩ b) s
    → (accept a Relation.Unary.∩ accept b) s
∩⇐ {s = []}     accept∘∩  = accept∘∩
∩⇐ {s = x ∷ xs} {a} {b} accept∘∩ = ∩⇐ (∩⇐ , ∩⇐)

-- complement
¬ : {Q Σ : Set} → DFA Q Σ → DFA Q Σ
¬ (dfa δ start accept) = dfa δ start (Relation.Unary.∁ accept)

¬⇒ : {Q Σ : Set} {s : String Σ} {a : DFA Q Σ}
    → Relation.Unary.∁ (accept a) s
    → accept (¬ a) s
¬⇒ = {!   !}

¬⇐ : {Q Σ : Set} {s : String Σ} {a : DFA Q Σ}
    → accept (¬ a) s
    → Relation.Unary.∁ (accept a) s
¬⇐ = {!   !}

-- DFA ⇒ NFA
DFA⇒NFA : {Q Σ : Set} → DFA Q Σ → NFA Q (Σ ⊎ E)
DFA⇒NFA (dfa δ startState acceptStates) = {!   !}
