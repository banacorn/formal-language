module Dist where

open import Data.Fin            using (Fin)
open import Data.Fin.Subset     using (Subset; ⁅_⁆)
                                renaming (_∪_ to _S∪_; _∩_ to _S∩_)
open import Data.Nat            using (ℕ)

infixr 5 _⊗_
infixr 3 _⨁_ _⨂_

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

FinSet = Dist Subset
FinElem = Dist Fin

--
--  FinSet
--

infix 4 _∪_ _∩_

-- insertion
insert : ∀ {t} → FinElem t → FinSet t → FinSet t
insert {   ⨀ x}  (⊙ e)     (⊙ s)     = ⊙ (⁅ e ⁆ S∪ s)
insert {tₒ ⨁ t₁} (⊕₀ e)    (⊕₀ s)    = ⊕₀ (insert e s)
insert {tₒ ⨁ t₁} (⊕₀ e)    (⊕₁ s)    = ⊕₁ s    -- element discarded, inserting to wrong set
insert {tₒ ⨁ t₁} (⊕₁ e)    (⊕₀ s)    = ⊕₀ s    -- element discarded, inserting to wrong set
insert {tₒ ⨁ t₁} (⊕₁ e)    (⊕₁ s)    = ⊕₁ (insert e s)
insert {tₒ ⨂ t₁} (e₀ ⊗ e₁) (s₀ ⊗ s₁) = insert e₀ s₀ ⊗ insert e₁ s₁

-- union
-- non-abelian, i.e., a ∪ b ≠ b ∪ a
_∪_ : ∀ {t} → FinSet t → FinSet t → FinSet t
⊙  a    ∪ ⊙  b    = ⊙  (a S∪ b)
⊕₀ a    ∪ ⊕₀ b    = ⊕₀ (a ∪ b)
⊕₀ a    ∪ ⊕₁ b    = ⊕₀ a          -- second set discarded!
⊕₁ a    ∪ ⊕₀ b    = ⊕₁ a          -- second set discarded!
⊕₁ a    ∪ ⊕₁ b    = ⊕₁ (a ∪ b)
a₀ ⊗ a₁ ∪ b₀ ⊗ b₁ = (a₀ ∪ b₀) ⊗ (a₁ ∪ b₁)

-- intersection
-- non-abelian, i.e., a ∪ b ≠ b ∪ a
_∩_ : ∀ {t} → FinSet t → FinSet t → FinSet t
⊙  a    ∩ ⊙  b    = ⊙  (a S∩ b)
⊕₀ a    ∩ ⊕₀ b    = ⊕₀ (a ∩ b)
⊕₀ a    ∩ ⊕₁ b    = ⊕₀ a
⊕₁ a    ∩ ⊕₀ b    = ⊕₁ a
⊕₁ a    ∩ ⊕₁ b    = ⊕₁ (a ∩ b)
a₀ ⊗ a₁ ∩ b₀ ⊗ b₁ = (a₀ ∩ b₀) ⊗ (a₁ ∩ b₁)
