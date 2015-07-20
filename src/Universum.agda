module Universum where

open import Data.Unit       using (⊤; tt)
open import Data.Sum        using (_⊎_; inj₁; inj₂)
open import Data.Product    using (_×_; _,_)

data Functor : Set₁ where
    I : Functor
    K : Set → Functor
    _⊕_ : Functor → Functor → Functor
    _⊗_ : Functor → Functor → Functor

-- the decoder, better viewed as Functor → Function
⟦_⟧ : Functor → (Set → Set)
⟦ I      ⟧ X = X
⟦ K A    ⟧ X = A                    -- constant
⟦ F ⊕ G ⟧ X = ⟦ F ⟧ X ⊎ ⟦ G ⟧ X
⟦ F ⊗ G ⟧ X = ⟦ F ⟧ X × ⟦ G ⟧ X

-- functor
map : ∀ {X Y} (F : Functor) → (X → Y) → (⟦ F ⟧ X → ⟦ F ⟧ Y)
map I       f x = f x
map (K A)   f x = x
map (F ⊕ G) f (inj₁ x) = inj₁ (map F f x)
map (F ⊕ G) f (inj₂ y) = inj₂ (map G f y)
map (F ⊗ G) f (l , r) = (map F f l) , (map G f r)

-- the least fixed point
data μ (F : Functor) : Set where
    ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F

Alg : Functor → Set → Set
Alg G X = ⟦ G ⟧ X → X


-- `fold` won't pass Agda's termination checking if it's defined like this
--      fold : ∀ {A} → (F : Functor) → Alg F A → μ F → A
--      fold F ϕ < x > = ϕ (map F (fold F ϕ) x)
-- so instead we will fuse map and fold first
--      mapFold F G ϕ x = map F (fold G ϕ) x

mapFold : ∀ {X} F G → Alg G X → ⟦ F ⟧ (μ G) → ⟦ F ⟧ X
mapFold I       H φ ⟨ x ⟩ = φ (mapFold H H φ x)
mapFold (K A)   H φ x = x
mapFold (F ⊕ G) H φ (inj₁ x) = inj₁ (mapFold F H φ x)
mapFold (F ⊕ G) H φ (inj₂ y) = inj₂ (mapFold G H φ y)
mapFold (F ⊗ G) H φ (l , r) = (mapFold F H φ l) , (mapFold G H φ r)

fold : ∀ {A} → (F : Functor) → Alg F A → μ F → A
fold F φ ⟨ x ⟩ = φ (mapFold F F φ x)


module Example where
    NatF : Functor
    NatF = K ⊤ ⊕ I

    Nat : Set
    Nat = μ NatF

    zero : Nat
    zero = ⟨ inj₁ tt ⟩

    suc : Nat → Nat
    suc n = ⟨ inj₂ n ⟩

    _+N_ : Nat → Nat → Nat
    ⟨ inj₁ tt ⟩ +N y = y
    ⟨ inj₂ x ⟩  +N y = ⟨ (inj₂ (x +N y)) ⟩

    ListF : Set → Functor
    ListF A = K ⊤ ⊕ (K A ⊗ I)

    List : Set → Set
    List A = μ (ListF A)

    nil : List Nat
    nil = ⟨ inj₁ tt ⟩

    cons : Nat → List Nat → List Nat
    cons x xs = ⟨ inj₂ (x , xs) ⟩

    _+L_ : ∀ {A} → List A → List A → List A
    ⟨ inj₁ nil ⟩ +L ys = ys
    ⟨ inj₂ (x , xs) ⟩ +L ys = ⟨ (inj₂ (x , (xs +L ys))) ⟩
