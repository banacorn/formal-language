module Example where

open import Automaton
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

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

acceptStates1 : Q1 -> Set
acceptStates1 q1 = ⊤
acceptStates1 _  = ⊥

DFA1 : DFA Q1 Σ1
DFA1 = dfa δ1 startState1 acceptStates1

str1 = c0 ∷ []
check1 : accept DFA1 str1
check1 = tt

str2 = c0 ∷ c1 ∷ []
check2 : accept DFA1 str2
check2 = tt

str3 = c0 ∷ c0 ∷ []
check3 : accept DFA1 str3
check3 = tt

str4 = c1 ∷ c1 ∷ c0 ∷ []
check4 : accept DFA1 str4
check4 = ?
