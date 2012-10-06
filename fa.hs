module FA (
    S(S),
    Language,
    State,
    States,
    Alphabet,
    Alphabets,
    Transition,
    NDTransition,
    ndtransition,
    negateFA,
    --unionFA,
    --intersectionFA,
    FA(NFA, DFA),
    transition,
    machine 
) where

import Data.Set
import Data.List (groupBy, intersperse)
import Test.QuickCheck


--  States
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
type NDTransition a = State a -> Alphabet -> States a

data FA a = DFA (States a) Alphabets (Transition a) (State a) (States a) 
          | NFA (States a) Alphabets (NDTransition a) (State a) (States a)

instance (Show a) => Show (S a) where
    show (S a) = show a
    show (a :. state) = (show a) ++ "-" ++ (show state)

transition :: (Eq a) => [(State a, Alphabet, State a)] -> Transition a
transition arcs state alphabet =
    let result = [ f | (s, a, f) <- arcs, s == state, a == alphabet ] in
    case result of [] -> error "Transition not deinfed"
                   [x] -> x

ndtransition :: (Eq a) => [(State a, Alphabet, States a)] -> NDTransition a
ndtransition arcs state alphabet = 
    let result = [ f | (s, a, f) <- arcs, s == state, a == alphabet ] in
    case result of [] -> empty
                   (x:xs) -> x

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

dropQuote :: String -> String
dropQuote [] = []
dropQuote ('"':xs) = dropQuote xs
dropQuote ('\'':xs) = dropQuote xs
dropQuote (x:xs) = x : dropQuote xs


showSet :: (Show a) => Set a -> String
showSet set = let list = toList set in
    case length list of 0 -> ""
                        1 -> show . head $ list
                        n -> concat . intersperse ", " . fmap show $ list



instance (Show a) => Show (FA a) where
    show (DFA states alphabets transition state accepts) = dropQuote $
        "DFA" ++
        "\n    states        : " ++ (show . fmap showSet . toList $ states) ++ 
        "\n    alphabets     : " ++ (show $ toList alphabets) ++
        "\n    transitions   : " ++ transitionList ++
        "\n    initial state : " ++ (show . showSet $ state) ++ 
        "\n    accept states : " ++ (show . fmap showSet . toList $ accepts) ++
        "\n"
        where transitionList = show [ (showSet state, alphabet, showSet $ transition state alphabet) | state <- toList states, alphabet <- toList alphabets ]
    show (NFA states alphabets transition state accepts) = dropQuote $ 
        "NFA" ++
        "\n    states        : " ++ (show . fmap showSet . toList $ states) ++ 
        "\n    alphabets     : " ++ (show $ toList alphabets) ++
        "\n    transitions   : " ++ transitionList ++
        "\n    initial state : " ++ (show . showSet $ state) ++ 
        "\n    accept states : " ++ (show . fmap showSet . toList $ accepts) ++
        "\n"
        where   transitionList = show [ (showSet state, alphabet, fmap showSet . toList $ transition state alphabet) | state <- toList states, alphabet <- toList extendedAlphabets, not $ Data.Set.null $ transition state alphabet ]
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



negateFA :: (Ord a) => FA a -> FA a
negateFA (DFA states a t s accepts) = DFA states a t s $ difference states accepts
negateFA (NFA states a t s accepts) = NFA states a t s $ difference states accepts



--(*.) :: (Ord a) => States a -> States a -> States a
--s0 *. s1 = 
--    fromList [ q0 *.. q1 | q0 <- toList s0, q1 <- toList s1]
--    where   q0 *.. q1 = fromList [ q0 :. S q1 | q0 <- toList s0, q1 <- toList s1]

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

