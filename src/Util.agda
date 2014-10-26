module Util where

open import Data.Bool           using (Bool; true; false)
open import Data.Nat            using (ℕ; zero; suc; _+_; _*_)
open import Data.Fin            using (Fin; fromℕ; inject₁; inject+)
                                renaming (zero to Fzero; suc to Fsuc)
open import Data.Fin.Subset     using (Subset; inside; outside; _∈_; _∉_)
open import Data.List           using (List)
                                renaming ([] to l[]; _∷_ to _l∷_; map to lmap)
open import Data.Vec            using (Vec; []; _∷_; _++_; replicate; reverse; lookup)
open import Data.Product        using (_×_; _,_)
open import Data.Sum            using (_⊎_; inj₁; inj₂)
open import Function            using (_∘_)
open import Relation.Nullary

--
--  Subset
--


_∈-Bool_ : ∀ {n} → (x : Fin n) → (p : Subset n) → Bool
x ∈-Bool p with lookup x p
... | inside = true
... | outside = false

-- build a list with elements collected from a subset
⇒List : ∀ {n} → Subset n → List (Fin n)
⇒List = ⇒List' ∘ reverse
    where   -- accepts reversed Subset representation
            ⇒List' : ∀ {n} → Subset n → List (Fin n)
            ⇒List' {zero}  [] = l[]
            ⇒List' {suc n} (inside  ∷ xs) = fromℕ n l∷ lmap inject₁ (⇒List' xs)
            ⇒List' {suc n} (outside ∷ xs) =            lmap inject₁ (⇒List' xs)


-- fits a smaller subset into the front of a larger subset
inj₁Subset : ∀ {m n} → Subset m → Subset (m + n)
inj₁Subset v = v ++ replicate outside

-- fits a smaller subset into the rare of a larger subset
inj₂Subset : ∀ {m n} → Subset m → Subset (n + m)
inj₂Subset {m} {n} v = replicate {_} {n} outside ++ v

--
--  Fin
--

-- given Fin (m + n)
-- determine whether it's coming from the "m" part or the "n" part
proj[_+_]_ : (m : ℕ) → (n : ℕ) → Fin (m + n) → Fin m ⊎ Fin n
proj[ zero + b ] x = inj₂ x
proj[ suc a + b ] Fzero = inj₁ Fzero
proj[ suc a + b ] Fsuc x = inject⊎ (proj[ a + b ] x)
    where   -- just read the fucking type
            inject⊎ : ∀ {m n} → Fin m ⊎ Fin n → Fin (suc m) ⊎ Fin n
            inject⊎ (inj₁ x) = inj₁ (inject₁ x)
            inject⊎ (inj₂ y) = inj₂ y

-- given Fin (m * n)
-- determine whether it's "coordinate" (m, n)
-- proj[_*_]_ : (m : ℕ) → (n : ℕ) → Fin (m * n) → Fin m × Fin n
-- proj[ a * b ] x = {!   !}
