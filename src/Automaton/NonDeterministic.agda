module Automaton.NonDeterministic where

open import Automaton.Types using (String)

open import Data.Empty          using (⊥)
open import Data.Bool           using (Bool)
open import Data.List           using (List; []; _∷_)
open import Data.Vec            using (Vec)
                                renaming ([] to []v; _∷_ to _∷v_)
open import Data.Nat            using (ℕ; suc)
open import Data.Fin            using (Fin)
open import Data.Sum            using (_⊎_)
open import Data.Unit           using (⊤)
open import Relation.Unary      using (_∈_; Empty)
open import Relation.Nullary    using (Dec; yes; no)
import Relation.Unary           as RU

open import FinSet              using (FinSet; _∪_; embed; singleton)

-- ε, the "empty" character
data E : Set where
    ε : E

-- Finite State & Alphabet
Q = Fin
Σ = Fin

record NFA (q : ℕ) (σ : ℕ) : Set₁ where
    constructor nfa
    field
        δ : Q q → (Σ σ ⊎ E) → FinSet q
        startState : Q q
        acceptStates : FinSet q

open NFA

-- run : ∀ {m n} → NFA m n → Q m → String (Σ n) → Set
-- run m state [] = state ∈ acceptStates m
-- run m state (x ∷ xs) = {!   !}

-- closure of Choices formed by collecting states reachable by ε
ε-closure : ∀ {q σ} → NFA q σ → Q q → FinSet q
ε-closure m state = singleton state ∪ δ m state (Data.Sum.inj₂ ε)

-- subset⇒list : ∀ {A} → Dec (A → Set) → List A

-- accept : {Q Σ : Set} → NFA Q Σ → String Σ → Set
-- accept m string = run m (startState m) string
