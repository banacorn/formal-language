module Util where

open import Data.Fin            using (Fin; fromℕ; inject₁)
open import Data.Fin.Subset     using (Subset; inside; outside)
open import Data.Nat            using (ℕ; zero; suc)
open import Data.Vec            using (Vec; []; _∷_; reverse)
open import Data.List           using (List)
                                renaming ([] to l[]; _∷_ to _l∷_; map to lmap)
open import Function            using (_∘_)

-- accepts reversed Subset representation
⇒List' : ∀ {n} → Subset n → List (Fin n)
⇒List' {zero}  [] = l[]
⇒List' {suc n} (inside  ∷ xs) = fromℕ n l∷ lmap inject₁ (⇒List' xs)
⇒List' {suc n} (outside ∷ xs) =            lmap inject₁ (⇒List' xs)

-- build a list with elements collected from a subset
⇒List : ∀ {n} → Subset n → List (Fin n)
⇒List = ⇒List' ∘ reverse
