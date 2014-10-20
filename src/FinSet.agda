module FinSet where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; _∨_; _∧_)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ; inject≤)
open import Data.Nat using (ℕ; _≤_)
                        renaming (zero to Nzero; suc to Nsuc)
open import Data.Vec using (Vec; []; _∷_; _++_; replicate; zipWith)
open import Relation.Nullary using (¬_)

-- represented by a vector of booleans, which indicates occurences of each elements
--
--  element   | t | f | t | t | f | t |
--  index     | 0 | 1 | 2 | 3 | 4 | 5 | nil
--

FinSet : ℕ → Set
FinSet = Vec Bool

infix 4 _∈_ _∉_

_∈_ : ∀ {n} → Fin n → FinSet n → Set
a     ∈ []           = ⊥
zero  ∈ (true  ∷ xs) = ⊤
zero  ∈ (false ∷ xs) = ⊥
suc a ∈ (x     ∷ xs) = a ∈ xs

_∉_ : ∀ {n} → Fin n → FinSet n → Set
a ∉ s = ¬ a ∈ s

singleton : ∀ {n} → Fin n → FinSet n
singleton {Nzero} a = []
singleton {Nsuc n} zero = true ∷ replicate {_} {n} false
singleton {Nsuc n} (suc a) = false ∷ singleton a

size : ∀ {n} → FinSet n → ℕ
size {n} _ = n

-- embedding smaller set to larger set
embed : ∀ {m n} → FinSet m → m ≤ n → FinSet n
embed []       _                  = replicate false
embed (x ∷ xs) (Data.Nat.s≤s m≤n) = x ∷ (embed xs m≤n)

_∪_ : ∀ {n} → FinSet n → FinSet n → FinSet n
_∪_ = zipWith _∨_

_∩_ : ∀ {n} → FinSet n → FinSet n → FinSet n
_∩_ = zipWith _∧_
