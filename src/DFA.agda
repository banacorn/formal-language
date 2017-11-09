module DFA where

open import Algebra using (BooleanAlgebra)
open import Level
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.List using (List; []; _∷_)
open import Data.List.Base using (foldr)
open import Data.Bool
open import Data.Bool.Properties as BoolProp using ()
 -- using (T-∧; T-≡; T-not-≡; not-¬)
open import Function
open import Function.Equivalence as FuncEq using (Equivalence; _⇔_)
open import Function.Equality using (Π)
-- open import Relation.Nullary.Decidable
open import Relation.Nullary using (Dec; yes; no) renaming (¬_ to ¬Rel_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality as Eq
    using (_≡_; _≢_; refl)

open Π
open Equivalence

String : (Σ : Set) → Set
String Σ = List Σ

-- A deterministic finite automaton is a 5-tuple, (Q, Σ, δ, q0, F)
record DFA (Q Σ : Set) : Set₁ where
    constructor dfa
    field
        δ : Q → Σ → Q
        initial : Q
        accepts : Q → Bool

open DFA

-- eats a character
step : {Q Σ : Set} → DFA Q Σ → Σ → DFA Q Σ
step (dfa δ initial accept) char = dfa δ (δ initial char) accept

-- eats a lot of characters
steps : {Q Σ : Set} → DFA Q Σ → String Σ → DFA Q Σ
steps machine [] = machine
steps machine (x ∷ xs) = steps (step machine x) xs

-- a machine M is acceptable if its initial state is in the accept states
acceptable : {Q Σ : Set} → DFA Q Σ → Bool
acceptable (dfa δ initial accepts) = accepts initial

--------------------------------------------------------------------------------
--  language and automaton
--------------------------------------------------------------------------------

_∈_ : {P Σ : Set} → String Σ → DFA P Σ → Set
string ∈ machine = T (acceptable (steps machine string))

_∉_ : {P Σ : Set} → String Σ → DFA P Σ → Set
string ∉ machine = Relation.Nullary.¬ (string ∈ machine)

_∈?_ : {P Σ : Set} → (string : String Σ) → (M : DFA P Σ) → Dec (string ∈ M)
string ∈? machine with acceptable (steps machine string)
string ∈? machine | false = no id
string ∈? machine | true = yes tt

--------------------------------------------------------------------------------
--  equivalence
--------------------------------------------------------------------------------

open import Relation.Binary

-- automaton equivalence is a heterogeneous binary relation
_≋_ : {P Q Σ : Set} → REL (DFA P Σ) (DFA Q Σ) _
A ≋ B = ∀ xs → xs ∈ A ⇔ xs ∈ B

⇔-setoid-isEquivalence : IsEquivalence {_} {zero} _⇔_
⇔-setoid-isEquivalence = Setoid.isEquivalence (FuncEq.⇔-setoid _)

≋-refl : {P Σ : Set} → Reflexive (_≋_ {P} {P} {Σ})
≋-refl _ = IsEquivalence.refl ⇔-setoid-isEquivalence

≋-sym : {P Q Σ : Set} → Sym (_≋_ {P} {Q} {Σ}) (_≋_ {Q} {P} {Σ})
≋-sym A≋B string = IsEquivalence.sym ⇔-setoid-isEquivalence (A≋B string)

≋-trans : {P Q R Σ : Set} → Trans (_≋_ {P} {Q} {Σ}) (_≋_ {Q} {R} {Σ}) (_≋_ {P} {R} {Σ})
≋-trans A≋B B≋C string = IsEquivalence.trans ⇔-setoid-isEquivalence (A≋B string) (B≋C string)

≋-isEquivalence : {P Σ : Set} → IsEquivalence (_≋_ {P} {P} {Σ})
≋-isEquivalence = record
    { refl = ≋-refl
    ; sym = ≋-sym
    ; trans = ≋-trans
    }

≋-setoid : (Q Σ : Set) → Setoid _ _
≋-setoid Q Σ = record
    { Carrier = DFA Q Σ
    ; _≈_ = _≋_
    ; isEquivalence = ≋-isEquivalence
    }


--------------------------------------------------------------------------------
--  product and sum
--------------------------------------------------------------------------------

-- a helper function for constructing a transition function with product states
product-δ : {P Q Σ : Set} → DFA P Σ → DFA Q Σ → P × Q → Σ → P × Q
product-δ A B (p , q) c = δ A p c , δ B q c

-- intersection
infixl 30 _∩_
_∩_ : {P Q Σ : Set} → DFA P Σ → DFA Q Σ → DFA (P × Q) Σ
A ∩ B = dfa
    (product-δ A B)
    (initial A , initial B)
    (uncurry λ p q → accepts A p ∧ accepts B q)

-- union
infixl 29 _∪_
_∪_ : {P Q Σ : Set} → DFA P Σ → DFA Q Σ → DFA (P × Q) Σ
A ∪ B = dfa
    (product-δ A B)
    (initial A , initial B)
    (uncurry λ p q → accepts A p ∨ accepts B q)

-- negation
infixl 31 ¬_
¬_ : {P Σ : Set} → DFA P Σ → DFA P Σ
¬ dfa δ₁ initial₁ accepts₁ = dfa δ₁ initial₁ (not ∘ accepts₁)

-- extracting one direction of a function equivalence
⟦_⟧→ : {A B : Set} → A ⇔ B → A → B
⟦ A⇔B ⟧→ A = to A⇔B ⟨$⟩ A

←⟦_⟧ : {A B : Set} → A ⇔ B → B → A
←⟦ A⇔B ⟧ B = from A⇔B ⟨$⟩ B

∈-∩-× : {P Q Σ : Set} → (A : DFA P Σ) → (B : DFA Q Σ) → (string : String Σ)
    → string ∈ A ∩ B
    → string ∈ A × string ∈ B
∈-∩-× A B []       ∈A∩B = ⟦ BoolProp.T-∧ ⟧→ ∈A∩B
∈-∩-× A B (x ∷ xs) ∈A∩B = ∈-∩-× (step A x) (step B x) xs ∈A∩B

∈-×-∩ : {P Q Σ : Set} → (A : DFA P Σ) → (B : DFA Q Σ) → (string : String Σ)
    → string ∈ A × string ∈ B
    → string ∈ A ∩ B
∈-×-∩ A B []       ∈A×∈B = ←⟦ BoolProp.T-∧ ⟧ ∈A×∈B
∈-×-∩ A B (x ∷ xs) ∈A×∈B = ∈-×-∩ (step A x) (step B x) xs ∈A×∈B

∈-∪-⊎ : {P Q Σ : Set} → (A : DFA P Σ) → (B : DFA Q Σ) → (string : String Σ)
    → string ∈ A ∪ B
    → string ∈ A ⊎ string ∈ B
∈-∪-⊎ A B []       ∈A∪B = ⟦ BoolProp.T-∨ ⟧→ ∈A∪B
∈-∪-⊎ A B (x ∷ xs) ∈A∪B = ∈-∪-⊎ (step A x) (step B x) xs ∈A∪B

∈-⊎-∪ : {P Q Σ : Set} → (A : DFA P Σ) → (B : DFA Q Σ) → (string : String Σ)
    → string ∈ A ⊎ string ∈ B
    → string ∈ A ∪ B
∈-⊎-∪ A B []       ∈A⊎∈B = ←⟦ BoolProp.T-∨ ⟧ ∈A⊎∈B
∈-⊎-∪ A B (x ∷ xs) ∈A⊎∈B = ∈-⊎-∪ (step A x) (step B x) xs ∈A⊎∈B

T-not-¬ : {b : Bool} → T (not b) → ¬Rel (T b)
T-not-¬ {false} P Q = Q
T-not-¬ {true} P Q = P

T-¬-not : {b : Bool} → ¬Rel (T b) → T (not b)
T-¬-not {false} P = tt
T-¬-not {true} P = P tt

¬⇒∉ : {P Σ : Set} → (M : DFA P Σ) → (string : String Σ)
    → string ∈ (¬ M)
    → string ∉ M
¬⇒∉ M []       = T-not-¬
¬⇒∉ M (x ∷ xs) = ¬⇒∉ (step M x) xs

∉⇒¬ : {P Σ : Set} → (M : DFA P Σ) → (string : String Σ)
    → string ∉ M
    → string ∈ (¬ M)
∉⇒¬ M []       = T-¬-not
∉⇒¬ M (x ∷ xs) = ∉⇒¬ (step M x) xs

Empty : {P Σ : Set} → DFA P Σ → Set
Empty M = ∄[ string ] (string ∈ M)

Universal : {P Σ : Set} → DFA P Σ → Set
Universal M = ∀ string → string ∈ M

complement-∩-Empty : {P Σ : Set} → (M : DFA P Σ) → Empty (M ∩ ¬ M)
complement-∩-Empty M ([] , ∈M∩¬M) =
    let
        P , ¬P = ∈-∩-× M (¬ M) [] ∈M∩¬M
    in contradiction P (¬⇒∉ M [] ¬P)
complement-∩-Empty M (x ∷ xs , ∈M∩¬M) =
    let
        M' = step M x
        P , ¬P = ∈-∩-× M' (¬ M') xs ∈M∩¬M
    in
        contradiction P (¬⇒∉ M (x ∷ xs) ¬P)

complement-∪-Universal : {P Σ : Set} → (M : DFA P Σ) → Universal (M ∪ ¬ M)
complement-∪-Universal M [] with [] ∈? M
complement-∪-Universal M [] | yes ∈M = ∈-⊎-∪ M (¬ M) [] (inj₁ ∈M)
complement-∪-Universal M [] | no  ∉M = ∈-⊎-∪ M (¬ M) [] (inj₂ (T-¬-not ∉M))
complement-∪-Universal M (x ∷ xs) = let
        M' =  step M     x
        ¬M' = step (¬ M) x
    in ∈-⊎-∪ M' ¬M' xs (∈-∪-⊎ M' ¬M' xs (complement-∪-Universal M' xs))

--------------------------------------------------------------------------------
--  concatenation
--------------------------------------------------------------------------------

infixl 28 _++_
_++_ : {P Q Σ : Set} → DFA P Σ → DFA Q Σ → DFA (P ⊎ Q) Σ
_++_ {P} {Q} {Σ} A B = dfa
    [ δ' , (λ q c → inj₂ (δ B q c)) ]
    (inj₁ (initial A))
    [ const false , accepts B ]
    where
        δ' : P → Σ → P ⊎ Q
        δ' state character with acceptable (step A character)
        δ' state character | false = inj₁ (δ A state character)
        δ' state character | true = inj₂ (initial B)

-- ++-right-identity : {P Q Σ : Set}
--     → (A : DFA P Σ) → (B : DFA Q Σ)
--     → Empty B
--     → DFA (P ⊎ Q) Σ

--------------------------------------------------------------------------------
--  Kleene closure
--------------------------------------------------------------------------------

infixl 32 _*
_* : {Q Σ : Set} → DFA Q Σ → DFA Q Σ
_* {Q} {Σ} M = dfa δ' (initial M) (accepts M)
    where
        δ' : Q → Σ → Q
        δ' state character with acceptable (step M character)
        δ' state character | false = δ M state character
        δ' state character | true = initial M
