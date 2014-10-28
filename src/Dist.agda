module Dist where

open import Data.Fin            using (Fin)
open import Data.Fin.Subset     using (Subset; ⁅_⁆; _∪_)
open import Data.Nat            using (ℕ)

infixr 4 _⊗_
infixr 2 _⨁_ _⨂_

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

insert : ∀ {t} → FinElem t → FinSet t → FinSet t
insert {   ⨀ x}  (⊙ e)    (⊙ s)      = ⊙ (⁅ e ⁆ ∪ s)
insert {tₒ ⨁ t₁} (⊕₀ e)   (⊕₀ s)     = ⊕₀ (insert e s)
insert {tₒ ⨁ t₁} (⊕₀ e)   (⊕₁ s)     = ⊕₁ s    -- element discarded, inserting to wrong set
insert {tₒ ⨁ t₁} (⊕₁ e)   (⊕₀ s)     = ⊕₀ s    -- element discarded, inserting to wrong set
insert {tₒ ⨁ t₁} (⊕₁ e)   (⊕₁ s)     = ⊕₁ (insert e s)
insert {tₒ ⨂ t₁} (e₀ ⊗ e₁) (s₀ ⊗ s₁) = insert e₀ s₀ ⊗ insert e₁ s₁
