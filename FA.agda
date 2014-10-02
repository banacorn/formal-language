open import Nat

--data Fin : ℕ -> Set where
--    fzero : {n : ℕ} -> Fin (succ n)
--    fsucc : {n : ℕ} -> Fin n -> Fin (succ n)
--
--data State (A : Set) : ℕ -> Set where
--    nominate : {n : ℕ} -> (A -> Fin n) -> State A n
--
--data Alphabet (A : Set) : ℕ -> Set where
--    nominate : {n : ℕ} -> (A -> Fin n) -> Alphabet A n

data Subset (A : Set) : Set₁ where
    ∈ : ((a : A) -> Set) -> Subset A

record DFA (Q : Set)  (Σ : Set) : Set₁ where
    constructor DFA[_,_,_]
    field
        δ : Q -> Σ -> Q
        startState : Q
        acceptStates : Subset Q

infixr 5 _::_
data String (Alphabet : Set): Set where
    nil : String Alphabet
    _::_ : Alphabet -> String Alphabet -> String Alphabet

run : {Q Σ : Set} -> DFA Q Σ -> Q -> String Σ -> Set
run M s (w0 :: w) = run M ((DFA.δ M) s w0) w
run M s nil with DFA.acceptStates M
run M s nil | ∈ f = f s

-- a language is regular iff some DFA recognizes it
Regular : {Q Σ : Set} -> DFA Q Σ -> String Σ -> Set
Regular M S = run M (DFA.startState M) S
