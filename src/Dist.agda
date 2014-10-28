module Dist where

open import Data.Fin            using (Fin)
open import Data.Fin.Subset     using (Subset)

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
