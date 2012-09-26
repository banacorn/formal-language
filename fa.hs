
module FA (
    State,
    Alphabet,
    Language,
    States,
    Alphabets,
    Transition,
    NDTransition,
    transition,
    ndtransition,
    machine 
) where

import Data.Set
import Test.QuickCheck

{-
    instance Arbitrary Char where
    arbitrary     = choose ('\32', '\128')
    coarbitrary c = variant (ord c `rem` 4)
-}


type State = String
type Alphabet = Char
type Language = String
type States = Set State
type Alphabets = Set Alphabet
type Transition = State -> Alphabet -> State
type NDTransition = State -> Alphabet -> States

data FA = DFA States Alphabets Transition State States | NFA States Alphabets NDTransition State States

transition :: Alphabets -> [(State, Alphabet, State)] -> Transition
transition alphabets tuple state alphabet = 
    [ ss | (s, a, [ss]) <- tuple, s == state, a == alphabet, member a alphabets]

ndtransition :: Alphabets -> [(State, Alphabet, [State])] -> NDTransition
ndtransition alphabets tuple state alphabet = 
    fromList [ ss | (s, a, [ss]) <- tuple, s == state, a == alphabet]
    where extendedAlphabets = insert ' ' alphabets

machine :: FA -> Language -> Bool
machine (DFA states alphabets transition state accepts) [] = member state accepts
machine (DFA states alphabets transition state accepts) (x:xs)
    | notMember x alphabets = False
    | otherwise = machine (DFA states alphabets transition nextState accepts) xs
    where   nextState = transition state x



machine (NFA states alphabets transition state accepts) [] = member state accepts
machine (NFA states alphabets transition state accepts) (x:xs)
    | notMember x alphabets = False
    | otherwise = or $ Prelude.map (\next -> machine (NFA states alphabets transition next accepts) xs ) nextState
    where   nextState   = toList $ union alphabet eta
            alphabet    = transition state x
            eta         = transition state ' '






nStates = fromList ["1", "2", "3", "4"]
nAlphabets = fromList ['0', '1']
nTransition = ndtransition nAlphabets [
    ("1", '0', ["2"]),
    ("1", ' ', ["3"]),
    ("2", '1', ["2", "4"]),
    ("3", ' ', ["2"]),
    ("3", '0', ["4"]),
    ("4", '0', ["3"])
    ]

nStart = "1"
nAccept = fromList ["3", "4"]



nfa = NFA nStates nAlphabets nTransition nStart nAccept
nm = machine nfa