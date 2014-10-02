module Test where

open import FA
open import Nat


-- example
--                 c0,c1
--               +------+
--        c0     |      |
-- (q0)------->[q1]<----+
--   |
--   | c1
--   +----->(q2)---+
--           ^     |c0,c1
--           |     |
--           +-----+
--

data Q1 : Set where
    q0 : Q1
    q1 : Q1
    q2 : Q1

data Σ1 : Set where
    c0 : Σ1
    c1 : Σ1

δ1 : Q1 -> Σ1 -> Q1
δ1 q0 c0 = q1
δ1 q0 c1 = q2
δ1 q1 c0 = q1
δ1 q1 c1 = q1
δ1 q2 c0 = q2
δ1 q2 c1 = q2

startState1 : Q1
startState1 = q0

acceptStates1 : Subset Q1
acceptStates1 = ∈ f
    where   f : Q1 -> Set
            f q1 = Top
            f _  = Bot

DFA1 : DFA Q1 Σ1
DFA1 = DFA[ δ1 , q0 , acceptStates1 ]


str1 = c0 :: nil
check1 : accept DFA1 str1
check1 = tt

str2 = c0 :: c1 :: nil
check2 : accept DFA1 str2
check2 = tt

str3 = c0 :: c0 :: nil
check3 : accept DFA1 str3
check3 = tt

-------------------------------------
-- for test vvv
-------------------------------------
--haha : {n m : ℕ} -> (State Q1 n) -> Q1 -> (Alphabet A1 m) -> A1 -> Fin n
--haha (nominate nq) q (nominate na) a = f (nq q) (na a)
--    where   f q0 c1 = q0
--            f q0 c2 = q
--haha : {n m : ℕ} {Q A : Set} -> State Q n -> Q -> Alphabet A m -> A -> State Q n
--haha (nominate nState) state (nominate nAlphabet) alphabet = nominate (λ w -> ? )

--a : Fin 3
--a = fzero {2}
--
--b : Fin 3
--b = fsucc (fzero {1})
--
--c : Fin 3
--c = fsucc (fsucc (fzero {0}))
--
--data Q : Set where
--    q₀ : Q
--
--f : Q -> Fin 1
--f q₀ = fzero {0}
--
--haha : State Q 1
--haha = nominate f
--
--haha2 : Alphabet Q 1
--haha2 = nominate f
-------------------------------------
--for test ^^^
-------------------------------------
