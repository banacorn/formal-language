module Relation.Unary.Membership {a} (A : Set a) where

open import Level
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Unary
open import Relation.Binary

infixl 4 _≋_
_≋_ : Rel (Pred A a) _
P ≋ Q = P ⊆′ Q × Q ⊆′ P

⊆-refl : Reflexive (_⊆′_ {a} {A} {a})
⊆-refl {pred} x P = P

≋-refl : Reflexive _≋_
≋-refl {pred} = (⊆-refl {pred}) , (⊆-refl {pred})

≋-sym : Symmetric _≋_
≋-sym x = (proj₂ x) , (proj₁ x)

≋-trans : Transitive _≋_
≋-trans f≋g g≋h =
    (λ x z → proj₁ g≋h x (proj₁ f≋g x z)) , (λ x z → proj₂ f≋g x (proj₂ g≋h x z))

≋-isEquivalence : IsEquivalence _≋_
≋-isEquivalence = record
    { refl = ≋-refl
    ; sym = ≋-sym
    ; trans = ≋-trans
    }

⊆-trans : Transitive (_⊆′_ {a} {A} {a})
⊆-trans A⊆B B⊆C x x∈A = B⊆C x (A⊆B x x∈A)

⊆-preorder : IsPreorder _≋_ _⊆′_
⊆-preorder = record
    { isEquivalence = ≋-isEquivalence
    ; reflexive = proj₁
    ; trans = ⊆-trans
    }

⊆-partialOrder : IsPartialOrder _≋_ _⊆′_
⊆-partialOrder = record
    { isPreorder = ⊆-preorder
    ; antisym = λ A⊆B B⊆A → A⊆B , B⊆A
    }

⊆-poset : Poset (suc a) a a
⊆-poset = record
    { Carrier = Pred A a
    ; _≈_ = _≋_
    ; _≤_ = _⊆′_
    ; isPartialOrder = ⊆-partialOrder
    }

module ⊆-Reasoning where
    import Relation.Binary.PartialOrderReasoning as PosetR
    open PosetR ⊆-poset public
        renaming (_≤⟨_⟩_ to _⊆⟨_⟩_)

    infix 1 _∈⟨_⟩_
    infixr 2 _→⟨_⟩_

    _∈⟨_⟩_ : ∀ x {xs ys} → x ∈ xs → xs IsRelatedTo ys → x ∈ ys
    x ∈⟨ x∈xs ⟩ xs⊆ys = begin_ xs⊆ys x x∈xs

    _→⟨_⟩_ : ∀ A {B C} → (A ⊆ B) → B IsRelatedTo C → A IsRelatedTo C
    A →⟨ f ⟩ B∼C = A ⊆⟨ (λ x x∈A → f x∈A) ⟩ B∼C
    -- A ⊆[ f ] relTo B∼C = A ⊆⟨ f ⟩ relTo B∼C
    --

        --(begin xs⊆ys) x∈xs
