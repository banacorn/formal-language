module FA (
    S(S),
    Language,
    State,
    States,
    Alphabet,
    Alphabets,

    Map(Map, NDMap),
    Mapping,
    NDMapping,

    driver,
    nddriver,
    mapping2ndmapping,

    epsilonClosure,
    flattenSet,
    dfa2nfa,
    --nfa2dfa,
    negateFA,
    --unionFA,
    --intersectionFA,
    FA(NFA, DFA),
    machine 
) where

import Data.Set 
import qualified Data.List as List
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

type Mapping a = (State a, Alphabet, State a)
type NDMapping a = (State a, Alphabet, States a)
data Map a = Map [Mapping a]
           | NDMap [NDMapping a]

data FA a = DFA (States a) Alphabets (Map a) (State a) (States a) 
          | NFA (States a) Alphabets (Map a) (State a) (States a)

instance (Show a) => Show (S a) where
    show (S a) = show a
    show (a :. state) = (show a) ++ "-" ++ (show state)

driver :: (Eq a, Show a) => Map a -> Transition a
driver (Map mappings) state alphabet =
    let result = [ f | (s, a, f) <- mappings, s == state, a == alphabet ] in
    case result of [] -> error $ show state ++ ", " ++ show alphabet ++ " Transition not deinfed"
                   [x] -> x

nddriver :: (Eq a) => Map a -> NDTransition a
nddriver (NDMap mappings) state alphabet = 
    let result = [ f | (s, a, f) <- mappings, s == state, a == alphabet ] in
    case result of [] -> empty
                   (x:xs) -> x

machine :: (Ord a, Show a) => FA a -> Language -> Bool
machine (DFA states alphabets mappings state accepts) [] = member state accepts
machine (DFA states alphabets mappings state accepts) (x:xs)
    | notMember x alphabets = False
    | otherwise = machine (DFA states alphabets mappings nextState accepts) xs
    where   nextState = (driver mappings) state x


machine (NFA states alphabets mappings state accepts) [] = or [accepted, epsilon]
    where   accepted = member state accepts 
            epsilon  = or $ fmap (\s -> member s accepts) $ toList $ (nddriver mappings) state ' '

machine (NFA states alphabets mappings state accepts) (x:xs)
    | not $ Data.Set.null $ driver state ' ' = True
    | notMember x alphabets = False
    | otherwise = or $ Prelude.map (\next -> machine (NFA states alphabets mappings next accepts) xs ) nextState
    where   
        driver      = nddriver mappings
        nextState   = toList $ union alphabet epsilon
        alphabet    = driver state x
        epsilon     = driver state ' '
        extendedAlphabets = insert ' ' alphabets

dropQuote :: String -> String
dropQuote [] = []
dropQuote ('"':xs) = dropQuote xs
dropQuote ('\\':xs) = dropQuote xs
dropQuote ('\'':xs) = dropQuote xs
dropQuote (x:xs) = x : dropQuote xs


showSet :: (Show a) => Set a -> String
showSet set = let list = toList set in
    case length list of 0 -> " @ "
                        1 -> " " ++ (show . head $ list) ++ " "
                        n -> " " ++ (concat . List.intersperse "." . fmap show $ list) ++ " "

powerset s
    | s == empty = singleton empty
    | otherwise = Data.Set.map (insert x) pxs `union` pxs
        where (x, xs) = deleteFindMin s
              pxs = powerset xs



states = fromList [
    singleton $ S "A", 
    singleton $ S "B",
    singleton $ S "C",
    singleton $ S "D"
    ]
alphabets = fromList ['0', '1']

mappings = Map [
    (singleton $ S "A", '1', singleton $ S "B"),
    (singleton $ S "A", '0', singleton $ S "A"),
    (singleton $ S "B", '1', singleton $ S "C"),
    (singleton $ S "B", '0', singleton $ S "A"),
    (singleton $ S "C", '1', singleton $ S "D"),
    (singleton $ S "C", '0', singleton $ S "B"),
    (singleton $ S "D", '1', singleton $ S "D"),
    (singleton $ S "D", '0', singleton $ S "C")
    ]

ndmappings = NDMap [
    (singleton $ S "A", '0', fromList [singleton $ S "B"]),
    (singleton $ S "A", ' ', fromList [singleton $ S "C"]),
    (singleton $ S "B", '1', fromList [singleton $ S "B", singleton $ S "D"]),
    (singleton $ S "C", ' ', fromList [singleton $ S "B"]),
    (singleton $ S "C", '0', fromList [singleton $ S "D"]),
    (singleton $ S "D", '0', fromList [singleton $ S "C"])
    ]
start = singleton $ S "A"
accepts = fromList [singleton $ S "C", singleton $ S "D"]

nfa = NFA states alphabets ndmappings start accepts
dfa = DFA states alphabets mappings start accepts

instance (Show a) => Show (Map a) where
    show (Map mappings) = dropQuote $ 
        listMapping mappings
        where
            listMapping = concat . fmap (prefixIndent . showMap)
            prefixIndent = (++) "\n                    "
            showMap (s, a, t) = 
                showSet s ++ 
                "* " ++ 
                show a ++ 
                " -> " ++ 
                (show . showSet $ t)
    show (NDMap mappings) = dropQuote $
        listMapping mappings
        where
            listMapping = concat . fmap (prefixIndent . showMap)
            prefixIndent = (++) "\n                    "
            showMap (s, a, t) = 
                showSet s ++ 
                "* " ++ 
                show a ++ 
                " -> " ++ 
                (show . fmap showSet . toList $ t)

instance (Show a) => Show (FA a) where
    show (DFA states alphabets mappings state accepts) = dropQuote $
        "DFA" ++
        "\n    states        : " ++ (show . fmap showSet . toList $ states) ++ 
        "\n    alphabets     : " ++ (show $ toList alphabets) ++
        "\n    transitions   : " ++ (show mappings) ++
        "\n    initial state : " ++ (show . showSet $ state) ++ 
        "\n    accept states : " ++ (show . fmap showSet . toList $ accepts) ++
        "\n"
    show (NFA states alphabets mappings state accepts) = dropQuote $ 
        "NFA" ++
        "\n    states        : " ++ (show . fmap showSet . toList $ states) ++ 
        "\n    alphabets     : " ++ (show $ toList alphabets) ++
        "\n    transitions   : " ++ (show mappings) ++
        "\n    initial state : " ++ (show . showSet $ state) ++ 
        "\n    accept states : " ++ (show . fmap showSet . toList $ accepts) ++
        "\n"


instance (Eq a) => Eq (FA a) where
    (==) (DFA states0 alphabets0 (Map mappings0) state0 accepts0) (DFA states1 alphabets1 (Map mappings1) state1 accepts1) = 
            states0 == states1
        &&  alphabets0 == alphabets1
        &&  mappings0 == mappings1
        &&  state0 == state1
        &&  accepts0 == accepts1
    (==) (NFA states0 alphabets0 (Map mappings0) state0 accepts0) (NFA states1 alphabets1 (Map mappings1) state1 accepts1) = 
            states0 == states1
        &&  alphabets0 == alphabets1
        &&  mappings0 == mappings1
        &&  state0 == state1
        &&  accepts0 == accepts1



negateFA :: (Ord a) => FA a -> FA a
negateFA (DFA states a m s accepts) = DFA states a m s $ difference states accepts
negateFA (NFA states a m s accepts) = NFA states a m s $ difference states accepts

mapping2ndmapping :: Mapping a -> NDMapping a
mapping2ndmapping (state, alphabet, target) = (state, alphabet, singleton target)
dfa2nfa :: FA a -> FA a
dfa2nfa (DFA s a (Map mappings) i f) = (NFA s a (NDMap ndmappings) i f)
    where ndmappings = fmap mapping2ndmapping mappings


--nfa2dfa :: (Ord a) => FA a -> FA a
nfa2dfa (NFA ndstates alphabets ndmappings ndstart ndaccepts) = 
    --Data.Set.map flattenSet $ powerset ndstates
    DFA states alphabets (Map mappings) start accepts
    where
        nddriver' = nddriver ndmappings
        powerstates = Data.Set.map flattenSet $ powerset ndstates
        mappings = []
        start = flattenSet $ epsilonClosure nddriver' ndstart
        accepts = ndaccepts



flattenSet :: (Ord a) => Set (Set a) -> Set a
flattenSet setset = Data.Set.foldl union empty setset


epsilonClosure :: (Ord a) => NDTransition a -> State a -> States a
epsilonClosure ndtransition state = insert state epsilonTransition
    where   epsilonTransition = flattenSet $ epsilonStatesSet
            epsilonStatesSet = Data.Set.map (epsilonClosure ndtransition) $ ndtransition state ' '


epsilonTransition :: (Ord a) => NDTransition a -> State a -> Alphabet -> State a
epsilonTransition ndtransition state alphabet = flattenSet $ ndtransition state alphabet


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