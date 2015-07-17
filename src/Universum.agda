module Universum where

open import Data.Unit       using (⊤)
open import Data.Sum        using (_⊎_; inj₁; inj₂)
open import Data.Product    using (_×_; _,_)

data Functor : Set₁ where
    I : Functor
    K : Set → Functor
    _⊕_ : Functor → Functor → Functor
    _⊗_ : Functor → Functor → Functor



-- the decoder
⟦_⟧ : Functor → Set → Set
⟦ I      ⟧ X = X
⟦ K A    ⟧ X = A
⟦ F ⊕ G ⟧ X = ⟦ F ⟧ X ⊎ ⟦ G ⟧ X
⟦ F ⊗ G ⟧ X = ⟦ F ⟧ X × ⟦ G ⟧ X

map : ∀ {X Y} (F : Functor) → (X → Y) → (⟦ F ⟧ X → ⟦ F ⟧ Y)
map I       f x = f x
map (K A)   f x = x
map (F ⊕ G) f (inj₁ x) = inj₁ (map F f x)
map (F ⊕ G) f (inj₂ y) = inj₂ (map G f y)
map (F ⊗ G) f (l , r) = (map F f l) , (map G f r)

data μ (F : Functor) : Set where
    ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F
