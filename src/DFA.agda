module DFA where

open import Level
open import Data.Unit
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; T; not)
open import Function
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary

open DecSetoid

String : (Σ : Set) → Set
String Σ = List Σ

-- A deterministic finite automaton is a 5-tuple, (Q, Σ, δ, q0, F)
record DFA (Q : DecSetoid zero zero) (Σ : Set): Set₁ where
    constructor dfa
    field
        δ : Carrier Q → Σ → Carrier Q
        initial : Carrier Q
        accepts : Carrier Q → Bool

open DFA

-- eats a character
step : ∀ {Q Σ} → DFA Q Σ → Σ → DFA Q Σ
step (dfa δ initial accept) char = dfa δ (δ initial char) accept

-- eats a lot of characters
steps : ∀ {Q Σ} → DFA Q Σ → String Σ → DFA Q Σ
steps machine []       = machine
steps machine (x ∷ xs) = steps (step machine x) xs

-- a machine M is acceptable if its initial state is in the accept states
acceptable : ∀ {Q Σ} → DFA Q Σ → Bool
acceptable (dfa δ initial accepts) = accepts initial

--------------------------------------------------------------------------------
--  language and automaton
--------------------------------------------------------------------------------

open import Relation.Unary hiding (Decidable)

Language : (Σ : Set) → Set _
Language Σ = Pred (String Σ) zero

-- machine ⇒ language
⟦_⟧ : ∀ {P Σ} → DFA P Σ → Language Σ
⟦ machine ⟧ = λ string → T (acceptable (steps machine string))

_∈?_ : ∀ {P Σ} → (string : String Σ) → (M : DFA P Σ) → Dec (string ∈ ⟦ M ⟧)
string ∈? machine with acceptable (steps machine string)
string ∈? machine | false = no id
string ∈? machine | true = yes tt

--------------------------------------------------------------------------------
--  product and sum
--------------------------------------------------------------------------------

open import Data.Product
open import Relation.Binary.Product.Pointwise

-- a helper function for constructing a transition function with product states
product-δ : ∀ {P Q Σ} → DFA P Σ → DFA Q Σ → Carrier P × Carrier Q → Σ → Carrier P × Carrier Q
product-δ A B (p , q) c = δ A p c , δ B q c

-- intersection
infixl 30 _∩ᴹ_
_∩ᴹ_ : ∀ {P Q Σ} → DFA P Σ → DFA Q Σ → DFA (P ×-decSetoid Q) Σ
A ∩ᴹ B = dfa
    (product-δ A B)
    (initial A , initial B)
    (uncurry (λ p q → accepts A p ∧ accepts B q))

-- union
infixl 29 _∪ᴹ_
_∪ᴹ_ : ∀ {P Q Σ} → DFA P Σ → DFA Q Σ → DFA (P ×-decSetoid Q) Σ
A ∪ᴹ B = dfa
    (product-δ A B)
    (initial A , initial B)
    (uncurry (λ p q → accepts A p ∨ accepts B q))

-- negation
infixl 31 Cᴹ_
Cᴹ_ : ∀ {P Σ} → DFA P Σ → DFA P Σ
Cᴹ dfa δ initial accepts = dfa δ initial (not ∘ accepts)

--------------------------------------------------------------------------------
--  concatenation
--------------------------------------------------------------------------------

open import Data.Sum
open import Relation.Binary.Sum
open import Data.Empty

module Pointwise where
    -- _⊎-decSetoid_ : ∀ {d₁ d₂ d₃ d₄}
    --     → DecSetoid d₁ d₂
    --     → DecSetoid d₃ d₄
    --     → DecSetoid _ _
    -- _⊎-decSetoid_ {d₁} {d₂} {d₃} {d₄} s₁ s₂ = record
    --     { Carrier = Carrier s₁ ⊎ Carrier s₂
    --     ; _≈_ = _⊎-≈_
    --     ; isDecEquivalence = record
    --         { isEquivalence = ⊎-≈-isEquivalence
    --         ; _≟_ = ⊎-≈-decidable
    --         }
    --     }
    --     where
    --
    --         open DecSetoid
    --         _⊎-≈_ : Carrier s₁ ⊎ Carrier s₂
    --             → Carrier s₁ ⊎ Carrier s₂
    --             → Set (d₂ ⊔ d₄)
    --         _⊎-≈_ (inj₁ x) (inj₁ y) = Lift {d₂} {d₄} (_≈_ s₁ x y)  -- (_≈_ s₁ x y)
    --         _⊎-≈_ (inj₁ x) (inj₂ y) = Lift ⊥
    --         _⊎-≈_ (inj₂ x) (inj₁ y) = Lift ⊥
    --         _⊎-≈_ (inj₂ x) (inj₂ y) = Lift {d₄} {d₂} (_≈_ s₂ x y)
    --
    --         open IsEquivalence
    --         module S₁ = IsDecEquivalence (isDecEquivalence s₁)
    --         module S₂ = IsDecEquivalence (isDecEquivalence s₂)
    --
    --         ⊎-≈-refl : Reflexive _⊎-≈_
    --         ⊎-≈-refl {inj₁ x} = lift (refl S₁.isEquivalence)
    --         ⊎-≈-refl {inj₂ y} = lift (refl S₂.isEquivalence)
    --
    --         ⊎-≈-sym : Symmetric _⊎-≈_
    --         ⊎-≈-sym {inj₁ x} {inj₁ y} (lift eq) = lift (sym S₁.isEquivalence eq)
    --         ⊎-≈-sym {inj₁ x} {inj₂ y} (lift ())
    --         ⊎-≈-sym {inj₂ x} {inj₁ y} (lift ())
    --         ⊎-≈-sym {inj₂ x} {inj₂ y} (lift eq) = lift (sym S₂.isEquivalence eq)
    --
    --         ⊎-≈-trans : Transitive _⊎-≈_
    --         ⊎-≈-trans {inj₁ x} {inj₁ y} {inj₁ z} (lift p) (lift q) = lift (trans S₁.isEquivalence p q)
    --         ⊎-≈-trans {inj₁ x} {inj₁ y} {inj₂ z} p        (lift ())
    --         ⊎-≈-trans {inj₁ x} {inj₂ y} {_}      (lift ()) q
    --         ⊎-≈-trans {inj₂ x} {inj₁ y} {_}      (lift ()) q
    --         ⊎-≈-trans {inj₂ x} {inj₂ y} {inj₁ z} p        (lift ())
    --         ⊎-≈-trans {inj₂ x} {inj₂ y} {inj₂ z} (lift p) (lift q) = lift (trans S₂.isEquivalence p q)
    --
    --         ⊎-≈-isEquivalence : IsEquivalence _⊎-≈_
    --         ⊎-≈-isEquivalence = record
    --             { refl = λ {x} → ⊎-≈-refl {x}
    --             ; sym = λ {x} {y} eq → ⊎-≈-sym {x} {y} eq
    --             ; trans = λ {x} {y} {z} p q → ⊎-≈-trans {x} {y} {z} p q
    --             }
    --
    --         lift-dec : ∀ {a} {b} {P : Set a} → Dec P → Dec (Lift {a} {b} P)
    --         lift-dec (yes p) = yes (lift p)
    --         lift-dec (no ¬p) = no (λ p → contradiction (lower p) ¬p)
    --
    --         ⊎-≈-decidable : Decidable _⊎-≈_
    --         ⊎-≈-decidable (inj₁ x) (inj₁ y) = lift-dec (S₁._≟_ x y)
    --         ⊎-≈-decidable (inj₁ x) (inj₂ y) = no lower
    --         ⊎-≈-decidable (inj₂ x) (inj₁ y) = no lower
    --         ⊎-≈-decidable (inj₂ x) (inj₂ y) = lift-dec (S₂._≟_ x y)


infixl 28 _++_
_++_ : ∀ {P Q Σ} → DFA P Σ → DFA Q Σ → DFA (P ⊎-decSetoid Q) Σ
_++_ {P} {Q} {Σ} A B = dfa
    δ'
    (inj₁ (initial A))
    accepts'
    where
        δ' : Carrier (P ⊎-decSetoid Q) → Σ → Carrier (P ⊎-decSetoid Q)
        δ' (inj₁ state) character with acceptable (step A character)
        δ' (inj₁ state) character | false = inj₁ (δ A state character)
        δ' (inj₁ state) character | true = inj₂ (initial B)
        δ' (inj₂ state) character = inj₂ (δ B state character)

        accepts' : Carrier (P ⊎-decSetoid Q) → Bool
        accepts' (inj₁ state) = false
        accepts' (inj₂ state) = accepts B state


-- -- ++-right-identity : {P Q Σ : Set}
-- --     → (A : DFA P Σ) → (B : DFA Q Σ)
-- --     → Empty B
-- --     → DFA (P ⊎ Q) Σ
--
--------------------------------------------------------------------------------
--  Kleene closure
--------------------------------------------------------------------------------

-- 1. make the initial state the accept state
-- 2. wire all of the transitions that would've gone to the original accept
--    states to the initial state (which is the new accept state)
infixl 32 _*
_* : ∀ {Q Σ} → DFA Q Σ → DFA Q Σ
_* {Q} {Σ} M = dfa δ' (initial M) accepts'
    where

        δ' : Carrier Q → Σ → Carrier Q
        δ' state character with acceptable (step M character)
        δ' state character | false = δ M state character
        δ' state character | true = initial M

        open IsDecEquivalence (isDecEquivalence Q) renaming (_≟_ to _≟s_)
        open import Relation.Nullary.Decidable
        accepts' : Carrier Q → Bool
        accepts' state = ⌊ state ≟s initial M ⌋

--------------------------------------------------------------------------------
--  Properties
--------------------------------------------------------------------------------

module Properties (Σ : Set) where

    open import Function.Equality using (Π)
    open Π
    open import Function.Equivalence using (_⇔_; Equivalence)
    open import Data.Bool.Properties as BoolProp
    open import Relation.Nullary.Negation
    -- extracting one direction of a function equivalence
    ⟦_⟧→ : {A B : Set} → A ⇔ B → A → B
    ⟦ A⇔B ⟧→ A = Equivalence.to A⇔B ⟨$⟩ A

    ←⟦_⟧ : {A B : Set} → A ⇔ B → B → A
    ←⟦ A⇔B ⟧ B = Equivalence.from A⇔B ⟨$⟩ B

    open import Relation.Unary.Membership (String Σ)
    open ⊆-Reasoning

    ∩-homo⇒ : ∀ {P Q} → (A : DFA P Σ) → (B : DFA Q Σ)
        → ⟦ A ∩ᴹ B ⟧ ⊆′ ⟦ A ⟧ ∩ ⟦ B ⟧
    ∩-homo⇒ A B []       = ⟦ BoolProp.T-∧ ⟧→
    ∩-homo⇒ A B (x ∷ xs) = ∩-homo⇒ (step A x) (step B x) xs

    ∩-homo⇐ : ∀ {P Q} → (A : DFA P Σ) → (B : DFA Q Σ)
        → ⟦ A ⟧ ∩ ⟦ B ⟧ ⊆′ ⟦ A ∩ᴹ B ⟧
    ∩-homo⇐ A B []       = ←⟦ BoolProp.T-∧ ⟧
    ∩-homo⇐ A B (x ∷ xs) = ∩-homo⇐ (step A x) (step B x) xs

    ∩-homo : ∀ {P Q} → (A : DFA P Σ) → (B : DFA Q Σ)
        → ⟦ A ∩ᴹ B ⟧ ≋ ⟦ A ⟧ ∩ ⟦ B ⟧
    ∩-homo A B = (∩-homo⇒ A B) , (∩-homo⇐ A B)

    ∩-sym⇒ : ∀ {P Q} → (A : DFA P Σ) → (B : DFA Q Σ)
        → ⟦ A ∩ᴹ B ⟧ ⊆′ ⟦ B ∩ᴹ A ⟧
    ∩-sym⇒ A B xs P =
            xs
        ∈⟨ P ⟩
            ⟦ A ∩ᴹ B ⟧
        ⊆⟨ ∩-homo⇒ A B ⟩
            ⟦ A ⟧ ∩ ⟦ B ⟧
        →⟨ swap ⟩
            ⟦ B ⟧ ∩ ⟦ A ⟧
        ⊆⟨ ∩-homo⇐ B A ⟩
            ⟦ B ∩ᴹ A ⟧
        ∎

    ∩-sym : ∀ {P Q} → (A : DFA P Σ) → (B : DFA Q Σ)
        → ⟦ A ∩ᴹ B ⟧ ≋ ⟦ B ∩ᴹ A ⟧
    ∩-sym A B = (∩-sym⇒ A B) , (∩-sym⇒ B A)

    ∪-homo⇒ : ∀ {P Q} → (A : DFA P Σ) → (B : DFA Q Σ)
        → ⟦ A ∪ᴹ B ⟧ ⊆′ ⟦ A ⟧ ∪ ⟦ B ⟧
    ∪-homo⇒ A B []       P = ⟦ BoolProp.T-∨ ⟧→ P
    ∪-homo⇒ A B (x ∷ xs) P = ∪-homo⇒ (step A x) (step B x) xs P

    ∪-homo⇐ : ∀ {P Q} → (A : DFA P Σ) → (B : DFA Q Σ)
        → ⟦ A ⟧ ∪ ⟦ B ⟧ ⊆′ ⟦ A ∪ᴹ B ⟧
    ∪-homo⇐ A B []       P = ←⟦ BoolProp.T-∨ ⟧ P
    ∪-homo⇐ A B (x ∷ xs) P = ∪-homo⇐ (step A x) (step B x) xs P

    ∪-homo : ∀ {P Q} → (A : DFA P Σ) → (B : DFA Q Σ)
        → ⟦ A ∪ᴹ B ⟧ ≋ ⟦ A ⟧ ∪ ⟦ B ⟧
    ∪-homo A B = (∪-homo⇒ A B) , (∪-homo⇐ A B)

    ∪-sym⇒ : ∀ {P Q} → (A : DFA P Σ) → (B : DFA Q Σ)
        → ⟦ A ∪ᴹ B ⟧ ⊆′ ⟦ B ∪ᴹ A ⟧
    ∪-sym⇒ A B xs P =
            xs
        ∈⟨ P ⟩
            ⟦ A ∪ᴹ B ⟧
        ⊆⟨ ∪-homo⇒ A B ⟩
            ⟦ A ⟧ ∪ ⟦ B ⟧
        →⟨ ⊎-swap ⟩
            ⟦ B ⟧ ∪ ⟦ A ⟧
        ⊆⟨ ∪-homo⇐ B A ⟩
            ⟦ B ∪ᴹ A ⟧
        ∎
        where
            ⊎-swap : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → B ⊎ A
            ⊎-swap (inj₁ x) = inj₂ x
            ⊎-swap (inj₂ y) = inj₁ y

    ∪-sym : ∀ {P Q} → (A : DFA P Σ) → (B : DFA Q Σ)
        → ⟦ A ∪ᴹ B ⟧ ≋ ⟦ B ∪ᴹ A ⟧
    ∪-sym A B = (∪-sym⇒ A B) , (∪-sym⇒ B A)

    T-not-¬ : {b : Bool} → T (not b) → ¬ (T b)
    T-not-¬ {false} P Q = Q
    T-not-¬ {true}  P Q = P

    T-¬-not : {b : Bool} → ¬ (T b) → T (not b)
    T-¬-not {false} P = tt
    T-¬-not {true}  P = P tt

    C⇒ : ∀ {P} → (M : DFA P Σ)
        → ∁ ⟦ M ⟧ ⊆ ⟦ Cᴹ M ⟧
    C⇒ M {[]}     = T-¬-not
    C⇒ M {x ∷ xs} = C⇒ (step M x) {xs}

    C⇐ : ∀ {P} → (M : DFA P Σ)
        → ⟦ Cᴹ M ⟧ ⊆ ∁ ⟦ M ⟧
    C⇐ M {[]}     = T-not-¬
    C⇐ M {x ∷ xs} = C⇐ (step M x) {xs}

    C-∩-∅⇒ : ∀ {P} → (M : DFA P Σ) → ⟦ M ∩ᴹ Cᴹ M ⟧ ⊆ ∅
    C-∩-∅⇒ M {[]} P =
        let
            Q , ¬Q = ∩-homo⇒ M (Cᴹ M) [] P
        in contradiction Q (C⇐ M {[]} ¬Q)
    C-∩-∅⇒ M {x ∷ xs} = C-∩-∅⇒ (step M x) {xs}

    C-∩-∅⇐ : ∀ {P} → (M : DFA P Σ) → ∅ ⊆ ⟦ M ∩ᴹ Cᴹ M ⟧
    C-∩-∅⇐ M {[]} ()
    C-∩-∅⇐ M {x ∷ xs} = C-∩-∅⇐ (step M x) {xs}

    C-∪-U⇒ : ∀ {P} → (M : DFA P Σ) → ⟦ M ∪ᴹ Cᴹ M ⟧ ⊆ U
    C-∪-U⇒ M {[]} P = tt
    C-∪-U⇒ M {x ∷ xs} = C-∪-U⇒ (step M x) {xs}

    C-∪-U⇐ : ∀ {P} → (M : DFA P Σ) → U ⊆ ⟦ M ∪ᴹ Cᴹ M ⟧
    C-∪-U⇐ M {[]} P with [] ∈? M
    C-∪-U⇐ M {[]} P | yes p = ←⟦ T-∨ ⟧ (inj₁ p)
    C-∪-U⇐ M {[]} P | no ¬p = ←⟦ T-∨
            {accepts M (initial M)}
            {not (accepts M (initial M))}
        ⟧ (inj₂ (T-¬-not ¬p))
    C-∪-U⇐ M {x ∷ xs} = C-∪-U⇐ (step M x) {xs}
