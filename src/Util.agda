module Util where

open import Data.Fin.Subset     using (Subset; inside; outside)
open import Data.Nat            using (ℕ; zero; suc; _+_)
open import Data.Fin            using (Fin; fromℕ; inject₁)
                                renaming (zero to Fzero; suc to Fsuc)
open import Data.Vec            using (Vec; []; _∷_; reverse)
open import Data.List           using (List)
                                renaming ([] to l[]; _∷_ to _l∷_; map to lmap)
open import Data.Sum            using (_⊎_; inj₁; inj₂)
open import Function            using (_∘_)



-- accepts reversed Subset representation
⇒List' : ∀ {n} → Subset n → List (Fin n)
⇒List' {zero}  [] = l[]
⇒List' {suc n} (inside  ∷ xs) = fromℕ n l∷ lmap inject₁ (⇒List' xs)
⇒List' {suc n} (outside ∷ xs) =            lmap inject₁ (⇒List' xs)

-- build a list with elements collected from a subset
⇒List : ∀ {n} → Subset n → List (Fin n)
⇒List = ⇒List' ∘ reverse


-- just read the fucking type
inject⊎₀ : ∀ {m n} → Fin m ⊎ Fin n → Fin (suc m) ⊎ Fin n
inject⊎₀ (inj₁ x) = inj₁ (inject₁ x)
inject⊎₀ (inj₂ y) = inj₂ y

-- given Fin (m + n), determine whether it's coming from the "m" part or the "n" part
inj[_+_]_ : (m : ℕ) → (n : ℕ) → Fin (m + n) → Fin m ⊎ Fin n
inj[ zero + b ] x = inj₂ x
inj[ suc a + b ] Fzero = inj₁ Fzero
inj[ suc a + b ] Fsuc x = inject⊎₀ (inj[ a + b ] x)
