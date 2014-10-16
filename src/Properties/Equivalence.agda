module Properties.Equivalence where

open import Automaton using (String)
open import Automaton.Deterministic using (DFA; accept; _∪_; _∩_; ¬)

open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Unary using (_∈_)
import Relation.Unary using (_∪_; _∩_; ∁)

∪⇒ : {Q₀ Q₁ Σ : Set} {s : String Σ} {a : DFA Q₀ Σ} {b : DFA Q₁ Σ}
    → (accept a Relation.Unary.∪ accept b) s
    → accept (a ∪ b) s
∪⇒ {s = []}     ∪∘accept  = ∪∘accept
∪⇒ {s = x ∷ xs} (inj₁ x₁) = {!   !}
∪⇒ {s = x ∷ xs} (inj₂ x₂) = {!   !}

∪⇐ : {Q₀ Q₁ Σ : Set} {s : String Σ} {a : DFA Q₀ Σ} {b : DFA Q₁ Σ}
    → accept (a ∪ b) s
    → (accept a Relation.Unary.∪ accept b) s
∪⇐ {s = []}     accept∘∪ = accept∘∪
∪⇐ {s = x ∷ xs} accept∘∪ = {!   !}


∩⇒ : {Q₀ Q₁ Σ : Set} {s : String Σ} {a : DFA Q₀ Σ} {b : DFA Q₁ Σ}
    → (accept a Relation.Unary.∩ accept b) s
    → accept (a ∩ b) s
∩⇒ {s = []}     ∩∘accept  = ∩∘accept
∩⇒ {s = x ∷ xs} (proj₁ , proj₂) = {!   !}

∩⇐ : {Q₀ Q₁ Σ : Set} {s : String Σ} {a : DFA Q₀ Σ} {b : DFA Q₁ Σ}
    → accept (a ∩ b) s
    → (accept a Relation.Unary.∩ accept b) s
∩⇐ {s = []}     accept∘∩  = accept∘∩
∩⇐ {s = x ∷ xs} {a} {b} accept∘∩ = {!   !}

¬⇒ : {Q Σ : Set} {s : String Σ} {a : DFA Q Σ}
    → Relation.Unary.∁ (accept a) s
    → accept (¬ a) s
¬⇒ = {!   !}

¬⇐ : {Q Σ : Set} {s : String Σ} {a : DFA Q Σ}
    → accept (¬ a) s
    → Relation.Unary.∁ (accept a) s
¬⇐ = {!   !}
