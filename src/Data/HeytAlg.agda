module Data.HeytAlg where

open import Data.Fin            using (Fin; fromℕ; inject₁)
                                renaming (zero to Fzero; suc to Fsuc)
open import Data.Fin.Subset     using (Subset; Side; inside; outside; ⁅_⁆)
                                renaming (_∪_ to _S∪_; _∩_ to _S∩_; _∈_ to _S∈_)
open import Data.List           using (List; []; _∷_; map; zipWith)
open import Data.Vec            using (Vec; lookup; reverse)
                                renaming ([] to v[]; _∷_ to _v∷_; map to vmap)
open import Data.Nat            using (ℕ; zero; suc; _+_; _*_)
open import Data.Empty          using (⊥)
open import Data.Bool           using (Bool; true; false; _∧_; not)
import      Relation.Unary      as RU
open import Function            using (_∘_)

infixr 5 _⊗_
infixr 3 _⨁_ _⨂_ _^_
-- infix 4 _∈-Bool_ _∈_
--infix 4 _∪_ _∩_

-- Supposely it's bicartesian closed and a poset
-- but I have no idea what Heyting Algebra has something to do with this
-- ** Just some cool names **
data HeytAlg : Set where
    ⨀   : ℕ → HeytAlg
    _⨁_ : HeytAlg → HeytAlg → HeytAlg         -- coproduct
    _⨂_ : HeytAlg → HeytAlg → HeytAlg         -- product
    _^_ : HeytAlg → HeytAlg → HeytAlg         -- exponential

-- Carrying something indexed by ℕ
data Structure (S : ℕ → Set) : HeytAlg → Set where
    ⊙    : ∀ {m  } → S m                       → Structure S (  ⨀ m)
    -- coproduct
    ⊕₀   : ∀ {m n} → Structure S m               → Structure S (m ⨁ n)
    ⊕₁   : ∀ {m n} → Structure S n               → Structure S (m ⨁ n)
    -- product
    _⊗_  : ∀ {m n} → Structure S m → Structure S n → Structure S (m ⨂ n)
    -- exponential
    ⊜    : ∀ {m n} → Structure (Vec (Structure S m)) n → Structure S (m ^ n)

-- Structure be a functor, smap be the map
smap : ∀ {S T t} → (F : ∀ {x} → S x → T x) → Structure S t → Structure T t
smap f (⊙   x ) = ⊙ (f x)
smap f (⊕₀  a ) = ⊕₀ (smap f a)
smap f (⊕₁  a ) = ⊕₁ (smap f a)
smap f (a ⊗ a₁) = smap f a ⊗ smap f a₁
smap f (⊜   a ) = ⊜ (smap (vmap (smap f)) a)

-- Measuring the size
∣_∣ : HeytAlg → ℕ
∣    ⨀ s ∣ = s
∣ s₀ ⨁ s₁ ∣ = ∣ s₀ ∣ + ∣ s₁ ∣
∣ s₀ ⨂ s₁ ∣ = ∣ s₀ ∣ * ∣ s₁ ∣
∣ s₀ ^ s₁ ∣ with ∣ s₀ ∣
∣ s₀ ^ s₁ ∣ | n₀ with ∣ s₁ ∣
∣ s₀ ^ s₁ ∣ | n₀ | n₁ = n₀ ** n₁
    where   -- exponential
            _**_ : ℕ → ℕ → ℕ
            a ** zero = a
            a ** suc b = (a ** b) * b


------------------------------------------------------------------------
-- FinElem & FinSet

FinElem : HeytAlg → Set
FinElem = Structure Fin

FinSet : HeytAlg → Set
FinSet s = Structure Fin (⨀ 2 ^ s)

⇒Side : Structure Fin (⨀ 2) → Bool
⇒Side (⊙ Fzero) = outside
⇒Side (⊙ (Fsuc x)) = inside

⇒Subset : ∀ {t} → FinSet t → Structure Subset t
⇒Subset (⊜ (   ⊙ s )) = ⊙ (vmap ⇒Side s)
⇒Subset (⊜ (   ⊕₀ s)) = ⊕₀ (⇒Subset (⊜ s))
⇒Subset (⊜ (   ⊕₁ s)) = ⊕₁ (⇒Subset (⊜ s))
⇒Subset (⊜ (s₀ ⊗ s₁)) = (⇒Subset (⊜ s₀)) ⊗ (⇒Subset (⊜ s₁))
⇒Subset (⊜ (⊜ s)) = ⊜ (smap (vmap (smap (vmap ⇒Side))) s)

------------------------------------------------------------------------
-- Membership and subset predicates

{-}
_∈_ : ∀ {t} → FinElem t → FinSet t → Set
⊙ e ∈ ⊜ s = {!   !}
⊕₀ e ∈ s = {!   !}
⊕₁ e ∈ s = {!   !}
e₀ ⊗ e₁ ∈ s = {!   !}
⊜ e ∈ s = {!   !}



_∈-Bool_ : ∀ {t} → FinElem t → FinSet t → Bool
⊙  e    ∈-Bool ⊙  s with lookup e s
... | inside  = true
... | outside = false
⊕₀ e    ∈-Bool ⊕₀ s    = e ∈-Bool s
⊕₀ e    ∈-Bool ⊕₁ s    = false
⊕₁ e    ∈-Bool ⊕₀ s    = false
⊕₁ e    ∈-Bool ⊕₁ s    = e ∈-Bool s
e₀ ⊗ e₁ ∈-Bool s₀ ⊗ s₁ = (e₀ ∈-Bool s₀) ∧ (e₁ ∈-Bool s₁)
⊜  e    ∈-Bool ⊜  s    = {!   !}

------------------------------------------------------------------------
-- Set operations

-- Insertion

insert : ∀ {t} → FinElem t → FinSet t → FinSet t
insert {   ⨀ t}  (⊙ e)     (⊙ s)     = ⊙ (⁅ e ⁆ S∪ s)
insert {tₒ ⨁ t₁} (⊕₀ e)    (⊕₀ s)    = ⊕₀ (insert e s)
insert {tₒ ⨁ t₁} (⊕₀ e)    (⊕₁ s)    = ⊕₁ s    -- element discarded, inserting to wrong set
insert {tₒ ⨁ t₁} (⊕₁ e)    (⊕₀ s)    = ⊕₀ s    -- element discarded, inserting to wrong set
insert {tₒ ⨁ t₁} (⊕₁ e)    (⊕₁ s)    = ⊕₁ (insert e s)
insert {tₒ ⨂ t₁} (e₀ ⊗ e₁) (s₀ ⊗ s₁) = insert e₀ s₀ ⊗ insert e₁ s₁
insert {tₒ ^ t₁} (⊜ e)     (⊜ s)     = {!   !}

-- Union
-- non-abelian, i.e., a ∪ b ≠ b ∪ a

_∪_ : ∀ {t} → FinSet t → FinSet t → FinSet t
⊙  a    ∪ ⊙  b    = ⊙  (a S∪ b)
⊕₀ a    ∪ ⊕₀ b    = ⊕₀ (a ∪ b)
⊕₀ a    ∪ ⊕₁ b    = ⊕₀ a          -- second set discarded!
⊕₁ a    ∪ ⊕₀ b    = ⊕₁ a          -- second set discarded!
⊕₁ a    ∪ ⊕₁ b    = ⊕₁ (a ∪ b)
a₀ ⊗ a₁ ∪ b₀ ⊗ b₁ = (a₀ ∪ b₀) ⊗ (a₁ ∪ b₁)
⊜  e    ∪ ⊜  s    = {!   !}

-- Intersection
-- non-abelian, i.e., a ∪ b ≠ b ∪ a

_∩_ : ∀ {t} → FinSet t → FinSet t → FinSet t
⊙  a    ∩ ⊙  b    = ⊙  (a S∩ b)
⊕₀ a    ∩ ⊕₀ b    = ⊕₀ (a ∩ b)
⊕₀ a    ∩ ⊕₁ b    = ⊕₀ a
⊕₁ a    ∩ ⊕₀ b    = ⊕₁ a
⊕₁ a    ∩ ⊕₁ b    = ⊕₁ (a ∩ b)
a₀ ⊗ a₁ ∩ b₀ ⊗ b₁ = (a₀ ∩ b₀) ⊗ (a₁ ∩ b₁)
⊜  e    ∩ ⊜  s    = {!   !}

-- Complement

∁ : ∀ {t} → FinSet t → FinSet t
∁ (⊙ a)     = ⊙ (vmap not a)
∁ (⊕₀ a)    = ⊕₀ (∁ a)
∁ (⊕₁ a)    = ⊕₁ (∁ a)
∁ (a₀ ⊗ a₁) = (∁ a₀) ⊗ (∁ a₁)
∁ (⊜ a)     = {!   !}

------------------------------------------------------------------------
-- Utils & Convertions

-- build a list with elements collected from a subset
Subset⇒List : ∀ {n} → Subset n → List (Fin n)
Subset⇒List = tesbuS⇒List ∘ reverse
    where   -- accepts reversed Subset representation
            tesbuS⇒List : ∀ {n} → Subset n → List (Fin n)
            tesbuS⇒List {zero} xs = []
            tesbuS⇒List {suc n} (inside  v∷ xs) = fromℕ n ∷ map inject₁ (tesbuS⇒List xs)
            tesbuS⇒List {suc n} (outside v∷ xs) =           map inject₁ (tesbuS⇒List xs)

⇒List : ∀ {t} → FinSet t → List (FinElem t)
⇒List (⊙ a)   = map ⊙ (Subset⇒List a)
⇒List (⊕₀ a)  = map ⊕₀ (⇒List a)
⇒List (⊕₁ a)  = map ⊕₁ (⇒List a)
⇒List (a ⊗ b) = zipWith _⊗_ (⇒List a) (⇒List b)
⇒List (⊜ a)   = {!   !}
-}
