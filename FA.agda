open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

record DFA (Q : Set) (Σ : Set) : Set₁ where
    constructor dfa
    field
        δ : Q -> Σ -> Q
        startState : Q
        acceptStates : Q -> Set

String = List

run : {Q Σ : Set} -> DFA Q Σ -> Q -> String Σ -> Set
run M s (w0 ∷ w) = run M ((DFA.δ M) s w0) w
run M s [] = DFA.acceptStates M s

accept : {Q Σ : Set} -> DFA Q Σ -> String Σ -> Set
accept M S = run M (DFA.startState M) S

-- union
_∪_ : {Q₀ Q₁ Σ : Set} → DFA Q₀ Σ → DFA Q₁ Σ → DFA (Q₀ × Q₁) Σ
_∪_ {Q₀} {Q₁} {Σ} (dfa δ₀ start₀ accept₀) (dfa δ₁ start₁ accept₁) =
    dfa (λ {(q₀ , q₁) a → δ₀ q₀ a , δ₁ q₁ a})
        (start₀ , start₁)
        {!   !}

-- definition of Language
Language : Set₁
Language = {Σ : Set} → String Σ → Set
