open import Nat

data Fin : ℕ -> Set where
    fzero : {n : ℕ} -> Fin (succ n)
    fsucc : {n : ℕ} -> Fin n -> Fin (succ n)

a : Fin 3
a = fzero {2}

b : Fin 3
b = fsucc (fzero {1})

c : Fin 3
c = fsucc (fsucc (fzero {0}))

data Q : Set where
    q₀ : Q

data State (A : Set) : ℕ -> Set where
    enum : {n : ℕ} -> (A -> Fin n) -> State A n

f : Q -> Fin 1
f q₀ = fzero {0} 

haha : State Q 1
haha = enum f
