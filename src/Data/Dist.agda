module Data.Dist where

open import Data.Fin            using (Fin; fromℕ; inject₁)
open import Data.Fin.Subset     using (Subset; inside; outside; ⁅_⁆)
                                renaming (_∪_ to _S∪_; _∩_ to _S∩_; _∈_ to _S∈_)
open import Data.List           using (List; []; _∷_; map; zipWith)
open import Data.Vec            using (lookup; reverse)
                                renaming ([] to v[]; _∷_ to _v∷_; map to vmap)
open import Data.Nat            using (ℕ; zero; suc; _+_; _*_)
open import Data.Empty          using (⊥)
open import Data.Bool           using (Bool; true; false; _∧_; not)
import Relation.Unary           as RU
open import Function            using (_∘_)

infixr 5 _⊗_
infixr 3 _⨁_ _⨂_
infix 4 _∈-Bool_ _∈_
infix 4 _∪_ _∩_

data Structure : Set where
    ⨀   : ℕ → Structure
    _⨁_ : Structure → Structure → Structure         -- coproduct
    _⨂_ : Structure → Structure → Structure         -- product
    ℘   : Structure → Structure

data Dist (S : ℕ → Set) : Structure → Set where
    ⊙    : ∀ {m  } → S m                 → Dist S (  ⨀ m)
    -- "coproduct"
    ⊕₀   : ∀ {m n} → Dist S m            → Dist S (m ⨁ n)
    ⊕₁   : ∀ {m n} → Dist S n            → Dist S (m ⨁ n)
    -- "product"
    _⊗_  : ∀ {m n} → Dist S m → Dist S n → Dist S (m ⨂ n)

FinSet = Dist Subset
FinElem = Dist Fin

--
--  FinSet
--

------------------------------------------------------------------------
-- Membership and subset predicates

_∈_ : ∀ {t} → FinElem t → FinSet t → Set
⊙  e    ∈ ⊙  s    = e S∈ s
⊕₀ e    ∈ ⊕₀ s    = e ∈ s
⊕₀ e    ∈ ⊕₁ s    = ⊥
⊕₁ e    ∈ ⊕₀ s    = ⊥
⊕₁ e    ∈ ⊕₁ s    = e ∈ s
e₀ ⊗ e₁ ∈ s₀ ⊗ s₁ = (∈s₀ RU.∪ ∈s₁) (e₀ ⊗ e₁)
    where   ∈s₀ = λ { (e₀ ⊗ e₁) → e₀ ∈ s₀ }
            ∈s₁ = λ { (e₀ ⊗ e₁) → e₁ ∈ s₁ }

_∈-Bool_ : ∀ {t} → FinElem t → FinSet t → Bool
⊙  e    ∈-Bool ⊙  s with lookup e s
... | inside  = true
... | outside = false
⊕₀ e    ∈-Bool ⊕₀ s    = e ∈-Bool s
⊕₀ e    ∈-Bool ⊕₁ s    = false
⊕₁ e    ∈-Bool ⊕₀ s    = false
⊕₁ e    ∈-Bool ⊕₁ s    = e ∈-Bool s
e₀ ⊗ e₁ ∈-Bool s₀ ⊗ s₁ = (e₀ ∈-Bool s₀) ∧ (e₁ ∈-Bool s₁)

------------------------------------------------------------------------
-- Set operations

-- Insertion

insert : ∀ {t} → FinElem t → FinSet t → FinSet t
insert {   ⨀ x}  (⊙ e)     (⊙ s)     = ⊙ (⁅ e ⁆ S∪ s)
insert {tₒ ⨁ t₁} (⊕₀ e)    (⊕₀ s)    = ⊕₀ (insert e s)
insert {tₒ ⨁ t₁} (⊕₀ e)    (⊕₁ s)    = ⊕₁ s    -- element discarded, inserting to wrong set
insert {tₒ ⨁ t₁} (⊕₁ e)    (⊕₀ s)    = ⊕₀ s    -- element discarded, inserting to wrong set
insert {tₒ ⨁ t₁} (⊕₁ e)    (⊕₁ s)    = ⊕₁ (insert e s)
insert {tₒ ⨂ t₁} (e₀ ⊗ e₁) (s₀ ⊗ s₁) = insert e₀ s₀ ⊗ insert e₁ s₁

-- Union
-- non-abelian, i.e., a ∪ b ≠ b ∪ a

_∪_ : ∀ {t} → FinSet t → FinSet t → FinSet t
⊙  a    ∪ ⊙  b    = ⊙  (a S∪ b)
⊕₀ a    ∪ ⊕₀ b    = ⊕₀ (a ∪ b)
⊕₀ a    ∪ ⊕₁ b    = ⊕₀ a          -- second set discarded!
⊕₁ a    ∪ ⊕₀ b    = ⊕₁ a          -- second set discarded!
⊕₁ a    ∪ ⊕₁ b    = ⊕₁ (a ∪ b)
a₀ ⊗ a₁ ∪ b₀ ⊗ b₁ = (a₀ ∪ b₀) ⊗ (a₁ ∪ b₁)

-- Intersection
-- non-abelian, i.e., a ∪ b ≠ b ∪ a

_∩_ : ∀ {t} → FinSet t → FinSet t → FinSet t
⊙  a    ∩ ⊙  b    = ⊙  (a S∩ b)
⊕₀ a    ∩ ⊕₀ b    = ⊕₀ (a ∩ b)
⊕₀ a    ∩ ⊕₁ b    = ⊕₀ a
⊕₁ a    ∩ ⊕₀ b    = ⊕₁ a
⊕₁ a    ∩ ⊕₁ b    = ⊕₁ (a ∩ b)
a₀ ⊗ a₁ ∩ b₀ ⊗ b₁ = (a₀ ∩ b₀) ⊗ (a₁ ∩ b₁)

-- Complement

∁ : ∀ {t} → FinSet t → FinSet t
∁ (⊙ a)     = ⊙ (vmap not a)
∁ (⊕₀ a)    = ⊕₀ (∁ a)
∁ (⊕₁ a)    = ⊕₁ (∁ a)
∁ (a₀ ⊗ a₁) = (∁ a₀) ⊗ (∁ a₁)

------------------------------------------------------------------------
-- Utils & Convertions

size : Structure → ℕ
size (⨀ s) = s
size (s₀ ⨁ s₁) = size s₀ + size s₁
size (s₀ ⨂ s₁) = size s₀ * size s₁
size (℘ s) with size s
size (℘ s) | zero  = 1
size (℘ s) | suc t = suc t * 2

-- build a list with elements collected from a subset
Subset⇒List : ∀ {n} → Subset n → List (Fin n)
Subset⇒List = tesbuS⇒List ∘ reverse
    where   -- accepts reversed Subset representation
            tesbuS⇒List : ∀ {n} → Subset n → List (Fin n)
            tesbuS⇒List {zero} xs = []
            tesbuS⇒List {suc n} (inside  v∷ xs) = fromℕ n ∷ map inject₁ (tesbuS⇒List xs)
            tesbuS⇒List {suc n} (outside v∷ xs) =           map inject₁ (tesbuS⇒List xs)

⇒List : ∀ {t} → FinSet t → List (FinElem t)
⇒List (⊙ a)   = map ⊙ (Subset⇒List a)
⇒List (⊕₀ a)  = map ⊕₀ (⇒List a)
⇒List (⊕₁ a)  = map ⊕₁ (⇒List a)
⇒List (a ⊗ b) = zipWith _⊗_ (⇒List a) (⇒List b)
