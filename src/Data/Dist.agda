module Data.Dist where

import Data.Fin as Fin
open import Data.Fin            using (Fin; fromℕ; toℕ; inject₁)
open import Data.Fin.Subset     using (inside; outside; ⁅_⁆)
                                renaming (Subset to SubsetFin; _∪_ to _∪S_; _∩_ to _∩S_; _∈_ to _∈S_)
open import Data.List           using (List; []; _∷_; map; zipWith)
import Data.Vec as Vec
open import Data.Vec            using (lookup; reverse; replicate)
                                renaming ([] to []V; _∷_ to _∷V_; map to mapV; _++_ to _++V_)
open import Data.Nat            -- using (ℕ; zero; suc; _+_; _*_; compare)
open import Data.Empty          using (⊥)
open import Data.Bool           using (Bool; true; false; _∧_; not)
import Relation.Unary           as RU
open import Function            using (_∘_)
open import Relation.Nullary using (yes; no)
-- open import Relation.Binary.PropositionalEquality


infixr 5 _⊗_
infixr 3 _⨁_ _⨂_
infix 4 _∈-Bool_ _∈_
infix 4 _∪_ _∩_

data Structure : Set where
    ⨀   : ℕ → Structure
    _⨁_ : Structure → Structure → Structure         -- coproduct
    _⨂_ : Structure → Structure → Structure         -- product

data Dist (S : ℕ → Set) : Structure → Set where
    ⊙    : ∀ {m  } → S m                 → Dist S (  ⨀ m)
    -- "coproduct"
    ⊕₀   : ∀ {m n} → Dist S m            → Dist S (m ⨁ n)
    ⊕₁   : ∀ {m n} → Dist S n            → Dist S (m ⨁ n)
    -- "product"
    _⊗_  : ∀ {m n} → Dist S m → Dist S n → Dist S (m ⨂ n)

Subset : Structure → Set
Subset = Dist SubsetFin

Elem : Structure → Set
Elem = Dist Fin

--
--  Subset
--

------------------------------------------------------------------------
-- Membership and Subset predicates

_∈_ : ∀ {t} → Elem t → Subset t → Set
⊙  e    ∈ ⊙  s    = e ∈S s
⊕₀ e    ∈ ⊕₀ s    = e ∈ s
⊕₀ e    ∈ ⊕₁ s    = ⊥
⊕₁ e    ∈ ⊕₀ s    = ⊥
⊕₁ e    ∈ ⊕₁ s    = e ∈ s
e₀ ⊗ e₁ ∈ s₀ ⊗ s₁ = (∈s₀ RU.∪ ∈s₁) (e₀ ⊗ e₁)
    where   ∈s₀ = λ { (e₀ ⊗ e₁) → e₀ ∈ s₀ }
            ∈s₁ = λ { (e₀ ⊗ e₁) → e₁ ∈ s₁ }


_∈-Bool_ : ∀ {t} → Elem t → Subset t → Bool
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

insert : ∀ {t} → Elem t → Subset t → Subset t
insert {   ⨀ x}  (⊙ e)     (⊙ s)     = ⊙ (⁅ e ⁆ ∪S s)
insert {tₒ ⨁ t₁} (⊕₀ e)    (⊕₀ s)    = ⊕₀ (insert e s)
insert {tₒ ⨁ t₁} (⊕₀ e)    (⊕₁ s)    = ⊕₁ s    -- element discarded, inserting to wrong set
insert {tₒ ⨁ t₁} (⊕₁ e)    (⊕₀ s)    = ⊕₀ s    -- element discarded, inserting to wrong set
insert {tₒ ⨁ t₁} (⊕₁ e)    (⊕₁ s)    = ⊕₁ (insert e s)
insert {tₒ ⨂ t₁} (e₀ ⊗ e₁) (s₀ ⊗ s₁) = insert e₀ s₀ ⊗ insert e₁ s₁

-- Union
-- non-abelian, i.e., a ∪ b ≠ b ∪ a

_∪_ : ∀ {t} → Subset t → Subset t → Subset t
⊙  a    ∪ ⊙  b    = ⊙  (a ∪S b)
⊕₀ a    ∪ ⊕₀ b    = ⊕₀ (a ∪ b)
⊕₀ a    ∪ ⊕₁ b    = ⊕₀ a          -- second set discarded!
⊕₁ a    ∪ ⊕₀ b    = ⊕₁ a          -- second set discarded!
⊕₁ a    ∪ ⊕₁ b    = ⊕₁ (a ∪ b)
a₀ ⊗ a₁ ∪ b₀ ⊗ b₁ = (a₀ ∪ b₀) ⊗ (a₁ ∪ b₁)

-- Intersection
-- non-abelian, i.e., a ∪ b ≠ b ∪ a

_∩_ : ∀ {t} → Subset t → Subset t → Subset t
⊙  a    ∩ ⊙  b    = ⊙  (a ∩S b)
⊕₀ a    ∩ ⊕₀ b    = ⊕₀ (a ∩ b)
⊕₀ a    ∩ ⊕₁ b    = ⊕₀ a
⊕₁ a    ∩ ⊕₀ b    = ⊕₁ a
⊕₁ a    ∩ ⊕₁ b    = ⊕₁ (a ∩ b)
a₀ ⊗ a₁ ∩ b₀ ⊗ b₁ = (a₀ ∩ b₀) ⊗ (a₁ ∩ b₁)

-- Complement

∁ : ∀ {t} → Subset t → Subset t
∁ (⊙ a)     = ⊙ (mapV not a)
∁ (⊕₀ a)    = ⊕₀ (∁ a)
∁ (⊕₁ a)    = ⊕₁ (∁ a)
∁ (a₀ ⊗ a₁) = (∁ a₀) ⊗ (∁ a₁)

------------------------------------------------------------------------
-- Utils & Convertions

size : Structure → ℕ
size (⨀ s) = s
size (s₀ ⨁ s₁) = size s₀ + size s₁
size (s₀ ⨂ s₁) = size s₀ * size s₁

-- Fin.Subset to List, elements indexed in reverse order
-- e.g. [++-+] → [3, 2, 0]
-- FS→L : ∀ {n} → SubsetFin n → List (Fin n)
-- FS→L {zero}  []V       = []
-- FS→L {suc n} (inside  ∷V xs) = fromℕ n ∷ map inject₁ (FS→L xs)
-- FS→L {suc n} (outside ∷V xs) =           map inject₁ (FS→L xs)

-- Subset to List
-- S→L : ∀ {s} → Subset s → List (Elem s)
-- S→L (⊙ xs)    = map ⊙ (FS→L xs)
-- S→L (⊕₀ xs)   = map ⊕₀ (S→L xs)
-- S→L (⊕₁ ys)   = map ⊕₁ (S→L ys)
-- S→L (xs ⊗ ys) = zipWith _⊗_ (S→L xs) (S→L ys)


-- List to Fin.Subset
-- e.g. [3, 2, 0] → [++-+]
-- L→FS : ∀ {n} → List (Fin n) → SubsetFin n
-- L→FS []       = replicate outside
-- L→FS (x ∷ xs) = flipAt (toℕ x) (L→FS xs)
--     where   -- make the nth element inside (reverse indexed)
-- flipAt : ∀ {n} → ℕ → SubsetFin n → SubsetFin n
-- flipAt i []V = []V
-- flipAt {suc n} i (x ∷V xs) with compare n i
-- flipAt {suc .n}             .(suc (n + k)) (x ∷V xs) | less     n k = x      ∷V xs -- quit searching
-- flipAt {suc .n}             n              (x ∷V xs) | equal   .n   = inside ∷V xs -- found
-- flipAt {suc .(suc (i + k))} i              (x ∷V xs) | greater .i k = x      ∷V flipAt i xs -- keep searching
