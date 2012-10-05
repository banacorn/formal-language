module FA (
    S(S),
    Alphabet,
    Language,
    State,
    States,
    Alphabets,
    Transition,
    NDTransition,
    NDArc,
    ndtransition,
    Arc,
    negateFA,
    --unionFA,
    --intersectionFA,
    FA(NFA, DFA),
    transition,
    machine 
) where

import Data.Set
import Data.List (groupBy)
import Test.QuickCheck


--  State can be tricky
--  * set (powerset construction)
--  * set of set (non-determinism)
--  * cartesian product (union, intersection ... )

data S a = S a | a :. (S a) deriving (Ord, Eq)
type State a = Set (S a)
type States a = Set (State a)

type Alphabet = Char
type Language = [Alphabet]
type Alphabets = Set Alphabet
type Transition a = State a -> Alphabet -> State a
type Arc a = (State a, Alphabet, State a)
type NDArc a = (State a, Alphabet, States a)
type NDTransition a = State a -> Alphabet -> States a

data FA a = DFA (States a) Alphabets (Transition a) (State a) (States a) 
          | NFA (States a) Alphabets (NDTransition a) (State a) (States a)

instance (Show a) => Show (S a) where
    show (S a) = show a
    show (a :. state) = (show a) ++ "-" ++ (show state)

transition :: (Eq a) => [Arc a] -> Transition a
transition arcs state alphabet =
    let result = [ f | (s, a, f) <- arcs, s == state, a == alphabet ] in
    case result of [] -> error "Transition not deinfed"
                   [x] -> x

ndtransition :: (Eq a) => [NDArc a] -> NDTransition a
ndtransition arcs state alphabet = 
    let result = [ f | (s, a, f) <- arcs, s == state, a == alphabet ] in
    case result of [] -> empty
                   [x] -> x 

machine :: (Ord a) => FA a -> Language -> Bool
machine (DFA states alphabets transition state accepts) [] = member state accepts
machine (DFA states alphabets transition state accepts) (x:xs)
    | notMember x alphabets = False
    | otherwise = machine (DFA states alphabets transition nextState accepts) xs
    where   nextState = transition state x


machine (NFA states alphabets transition state accepts) [] = or [accepted, epsilon]
    where   accepted = member state accepts 
            epsilon  = or $ fmap (\s -> member s accepts) $ toList (transition state ' ')

machine (NFA states alphabets transition state accepts) (x:xs)
    | not $ Data.Set.null $ transition state ' ' = True
    | notMember x alphabets = False
    | otherwise = or $ Prelude.map (\next -> machine (NFA states alphabets transition next accepts) xs ) nextState
    where   nextState   = toList $ union alphabet epsilon
            alphabet    = transition state x
            epsilon     = transition state ' '
            extendedAlphabets = insert ' ' alphabets


instance (Show a) => Show (FA a) where
    show (DFA states alphabets transition state accepts) = 
        "DFA" ++
        "\n    states        : " ++ (show $ toList states) ++ 
        "\n    alphabets     : " ++ (show $ toList alphabets) ++
        "\n    transitions   : " ++ transitionList ++
        "\n    initial state : " ++ show state ++ 
        "\n    accept states : " ++ (show $ toList accepts)
        where transitionList = show [ (state, alphabet, transition state alphabet) | state <- toList states, alphabet <- toList alphabets ]
    show (NFA states alphabets transition state accepts) = 
        "NFA" ++
        "\n    states        : " ++ (show $ toList states) ++ 
        "\n    alphabets     : " ++ (show $ toList alphabets) ++
        "\n    transitions   : " ++ transitionList ++
        "\n    initial state : " ++ show state ++ 
        "\n    accept states : " ++ (show $ toList accepts)
        where   transitionList = show [ (state, alphabet, toList $ transition state alphabet) | state <- toList states, alphabet <- toList extendedAlphabets, not $ Data.Set.null $ transition state alphabet ]
                extendedAlphabets = insert ' ' alphabets
instance (Eq a) => Eq (FA a) where
    (==) (DFA states0 alphabets0 transition0 state0 accepts0) (DFA states1 alphabets1 transition1 state1 accepts1) = 
            states0 == states1
        &&  alphabets0 == alphabets1
        &&  transitionList0 == transitionList1
        &&  state0 == state1
        &&  accepts0 == accepts1
        where   transitionList0 = [ transition0 state alphabet | state <- toList states0, alphabet <- toList alphabets0 ]
                transitionList1 = [ transition1 state' alphabet' | state' <- toList states1, alphabet' <- toList alphabets1 ]


--(*.) :: (Ord a) => States a -> States a -> States a
--s0 *. s1 = 
--    fromList [ q0 :. S q1 | q0 <- toList s0, q1 <- toList s1]

negateFA :: (Ord a) => FA a -> FA a
negateFA (DFA states a t s accepts) = DFA states a t s $ difference states accepts

--unionFA :: (Ord a) => FA a -> FA a -> FA a
--unionFA (DFA states0 alphabets0 transition0 start0 accepts0) (DFA states1 alphabets1 transition1 start1 accepts1) =
--    DFA states alphabets0 transition start accepts
--    where   states = states0 *. states1
--            transition state a = Data.Set.map (transition' a) state
--                where   transition' a (s0 :. S s1) = next0 :. S next1
--                            where   (S next0) = transition0 (S s0) a
--                                    (S next1) = transition1 (S s1) a
--            start = singleton start0 :. S start1
--            accepts = union (states0 *. accepts1) (accepts0 *. states1)

--intersectionFA :: (Ord a) => FA a -> FA a -> FA a
--intersectionFA (DFA states0 alphabets0 transition0 (S start0) accepts0) (DFA states1 alphabets1 transition1 (S start1) accepts1) =
--    DFA states alphabets0 transition start accepts
--    where   states = states0 *. states1
--            transition (s0 :. S s1) a = next0 :. S next1
--                where   (S next0) = transition0 (S s0) a
--                        (S next1) = transition1 (S s1) a
--            start = start0 :. S start1
--            accepts = accepts0 *. accepts1




{-



    show (NFA states alphabets transition state accepts) = 
        "DFA " ++ (show $ toList states) ++ " " ++ (show $ toList alphabets) ++ " δ " ++ show state ++ " " ++ (show $ toList accepts)
    (==) (NFA states0 alphabets0 transition0 state0 accepts0) (NFA states1 alphabets1 transition1 state1 accepts1) = 
            states0 == states1
        &&  alphabets0 == alphabets1
        &&  fromList [ transition0 state alphabet | state <- toList states0, alphabet <- toList alphabets0 ] == fromList [ transition1 state alphabet | state <- toList states1, alphabet <- toList alphabets1 ]
        &&  state0 == state1
        &&  accepts0 == accepts1

-}  