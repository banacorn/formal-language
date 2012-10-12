{-# LANGUAGE UnicodeSyntax #-}

module Automaton (
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

    --epsilonClosure,
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
import Control.Applicative hiding (empty)
import qualified Data.List as List
import Test.QuickCheck

type State  = Int
type States = Set State

type Alphabet = Char
type Language = [Alphabet]
type Alphabets = Set Alphabet

type Transition = State -> Alphabet -> State
type NDTransition = State -> Alphabet -> States

type Mapping = (State, Alphabet, State)
type NDMapping = (State, Alphabet, States)
data Map = Map [Mapping]
           | NDMap [NDMapping]

data FA = DFA States Alphabets Map State States
          | NFA States Alphabets Map State States

smap :: (Ord a, Ord b) => (a -> b) -> (Set a) -> (Set b)
smap = Data.Set.map

--instance (Show a) => Show (S a) where
--    show (S a) = show a
--    show (a :. state) = (show a) ++ "-" ++ (show state)

driver :: Map -> Transition
driver (Map mappings) state alphabet =
    let result = [ f | (s, a, f) <- mappings, s == state, a == alphabet ] in
    case result of [] -> error $ show state ++ ", " ++ show alphabet ++ " Transition not deinfed"
                   [x] -> x

nddriver :: Map -> NDTransition
nddriver (NDMap mappings) state alphabet = 
    let result = [ f | (s, a, f) <- mappings, s == state, a == alphabet ] in
    case result of [] -> empty
                   (x:xs) -> x

machine :: FA -> Language -> Bool
machine (DFA states alphabets mappings state accepts) [] = member state accepts
machine (DFA states alphabets mappings state accepts) (x:xs)
    | notMember x alphabets = False
    | otherwise = machine (DFA states alphabets mappings nextState accepts) xs
    where   nextState = (driver mappings) state x


machine (NFA states alphabets mappings state accepts) [] = or [accepted, epsilon]
    where   accepted = member state accepts 
            epsilon  = or $ fmap (\s -> member s accepts) $ toList $ (nddriver mappings) state ' '

machine (NFA states alphabets mappings state accepts) (x:xs)
    | not $ Data.Set.null $ transit state ' ' = True
    | notMember x alphabets = False
    | otherwise = or $ Prelude.map (\next -> machine (NFA states alphabets mappings next accepts) xs ) nextState
    where   
        transit     = nddriver mappings
        nextState   = toList $ union alphabet epsilon
        alphabet    = transit state x
        epsilon     = transit state ' '
        extendedAlphabets = insert ' ' alphabets

dropQuote :: String -> String
dropQuote [] = []
dropQuote ('"':xs) = dropQuote xs
dropQuote ('\\':xs) = dropQuote xs
dropQuote ('\'':xs) = dropQuote xs
dropQuote ('8':'7':'0':'9':xs) = '∅' : dropQuote xs
dropQuote (x:xs) = x : dropQuote xs

states = fromList [0..1]
alphabets = fromList ['a', 'b']

mappings = Map [
    (0, 'b', 1),
    (0, 'a', 0),
    (1, 'b', 1),
    (1, 'a', 0)
    ]


--ndmappings = NDMap [
--    (singleton $ S "A", '0', fromList [singleton $ S "B"]),
--    (singleton $ S "A", ' ', fromList [singleton $ S "C"]),
--    (singleton $ S "B", '1', fromList [singleton $ S "B", singleton $ S "D"]),
--    (singleton $ S "C", ' ', fromList [singleton $ S "B"]),
--    (singleton $ S "C", '0', fromList [singleton $ S "D"]),
--    (singleton $ S "D", '0', fromList [singleton $ S "C"])
--    ]
start = 0
accepts = fromList [1]



statesA = fromList [2..3]
mappingsA = Map [
    (2, 'b', 3),
    (2, 'a', 2),
    (3, 'b', 3),
    (3, 'a', 2)
    ]

startA = 2
acceptsA = fromList [3]



--nfa = NFA states alphabets ndmappings start accepts
dfa = DFA states alphabets mappings start accepts
dfaa = DFA statesA alphabets mappingsA startA acceptsA

u = dfa `unionFA` dfaa

instance Show Map where
    show (Map mappings) = dropQuote $ 
        listMapping mappings
        where
            listMapping = concat . fmap (prefixIndent . showMap)
            prefixIndent = (++) "\n        "
            showMap (s, a, t) = 
                show s ++ 
                "  ×  " ++ 
                show a ++ 
                "  →  " ++ 
                show t
    show (NDMap mappings) = dropQuote $
        listMapping mappings
        where
            listMapping = concat . fmap (prefixIndent . showMap)
            prefixIndent = (++) "\n        "
            showMap (s, a, t) = 
                show s ++ 
                "  ×  " ++ 
                show a ++ 
                "  →  " ++ 
                (show . toList $ t)

instance Show FA where
    show (DFA states alphabets mappings state accepts) = dropQuote $
        "DFA" ++
        "\n    Q   " ++ (show . toList $ states) ++ 
        "\n    Σ   " ++ (show $ toList alphabets) ++
        "\n    δ   " ++ (show mappings) ++
        "\n    q   " ++ (show state) ++ 
        "\n    F   " ++ (show . toList $ accepts) ++
        "\n"
    show (NFA states alphabets mappings state accepts) = dropQuote $ 
        "NFA" ++
        "\n    Q   " ++ (show . toList $ states) ++ 
        "\n    Σ   " ++ (show $ toList alphabets) ++
        "\n    δ   " ++ (show mappings) ++
        "\n    q   " ++ (show state) ++ 
        "\n    F   " ++ (show . toList $ accepts) ++
        "\n"


instance Eq FA where
    (==) (DFA states0 alphabets0 (Map mappings0) state0 accepts0) (DFA states1 alphabets1 (Map mappings1) state1 accepts1) = 
            states0 == states1
        &&  alphabets0 == alphabets1
        &&  mappings0 == mappings1
        &&  state0 == state1
        &&  accepts0 == accepts1
    (==) (NFA states0 alphabets0 (NDMap mappings0) state0 accepts0) (NFA states1 alphabets1 (NDMap mappings1) state1 accepts1) = 
            states0 == states1
        &&  alphabets0 == alphabets1
        &&  mappings0 == mappings1
        &&  state0 == state1
        &&  accepts0 == accepts1



--negateFA :: (Ord a) => FA a -> FA a
negateFA (DFA states a m s accepts) = DFA states a m s $ difference states accepts
negateFA (NFA states a m s accepts) = NFA states a m s $ difference states accepts

--mapping2ndmapping :: Mapping a -> NDMapping a
mapping2ndmapping (state, alphabet, target) = (state, alphabet, singleton target)


--dfa2nfa :: FA a -> FA a
dfa2nfa (DFA s a (Map mappings) i f) = (NFA s a (NDMap ndmappings) i f)
    where ndmappings = fmap mapping2ndmapping mappings


encodePair :: (Eq a1, Eq a) => (Set a, Set a1) -> (a, a1) -> Int
encodePair (setA, setB) (a, b) = index
    where   listA = toList setA
            listB = toList setB
            indexA = List.elemIndex a listA
            indexB = List.elemIndex b listB
            base = fmap (* size setB) indexA 
            index = case (+) <$> base <*> indexB of Just a -> a
                                                    Nothing -> 0


unionFA :: FA -> FA -> FA
unionFA (DFA states0 alphabets mappings0 start0 accepts0) (DFA states1 _ mappings1 start1 accepts1) =
    DFA states alphabets mappings start accepts
    where
        stateSpace = size states0 * size states1
        encode = encodePair (states0, states1)
        driver0 = driver mappings0
        driver1 = driver mappings1

        states = fromList [0 .. stateSpace - 1]
        mappings = Map [ (encode (s0, s1), a, encode (driver0 s0 a, driver1 s1 a)) | a <- toList alphabets , s0 <- toList states0, s1 <- toList states1 ]
        start = encode (start0, start1)
        accepts = fromList $ concat [ prod0 a | a <- toList accepts0 ] ++ concat [ prod1 a | a <- toList accepts1 ]
            where prod0 a = [ encode (a, s) | s <- toList states1 ]
                  prod1 a = [ encode (s, a) | s <- toList states0 ]



--intersectionFA :: FA -> FA -> FA
intersectionFA (DFA states0 alphabets mappings0 start0 accepts0) (DFA states1 _ mappings1 start1 accepts1) =
    DFA states alphabets mappings start accepts
    where
        stateSpace = size states0 * size states1
        encode = encodePair (states0, states1)
        driver0 = driver mappings0
        driver1 = driver mappings1

        states = fromList [0 .. stateSpace - 1]
        mappings = Map [ (encode (s0, s1), a, encode (driver0 s0 a, driver1 s1 a)) | a <- toList alphabets , s0 <- toList states0, s1 <- toList states1 ]
        start = encode (start0, start1)
        accepts = fromList [ encode (a0, a1) | a0 <- toList accepts0, a1 <- toList accepts1 ]

--nfa2dfa :: (Ord a) => FA a -> FA a
--nfa2dfa (NFA ndstates alphabets ndmappings ndstart ndaccepts) = 
--    DFA states alphabets mappings start accepts
--    where
--        transit = epsilonTransition ndmappings
--        start = epsilonClosure ndmappings ndstart
--        states = collectStates ndmappings alphabets (empty, singleton start)
--        mappings = Map [ (state, alphabet, transit state alphabet) | state <- toList states, alphabet <- toList alphabets ]
--        accepts = Data.Set.filter (\ newState ->
--                not . and . toList $ Data.Set.map (\ acceptState -> Data.Set.null $ acceptState `intersection` newState ) ndaccepts
--            ) states

--flattenSet :: (Ord a) => Set (Set a) -> Set a
flattenSet setset = Data.Set.foldl union empty setset


--epsilonClosure :: (Ord a) => Map a -> State a -> State a
--epsilonClosure mappings state = flattenSet $ insert state epsilonTransition
--    where   nddriver' = nddriver mappings
--            epsilonTransition = epsilonStatesSet
--            epsilonStatesSet = smap (epsilonClosure mappings) $ nddriver' state ' '


----epsilonTransition :: (Ord a) => Map a -> State a -> Alphabet -> State a
--epsilonTransition mappings state alphabet =
--    let 
--        states = smap singleton $ epsilonClosure mappings state 
--        result = smap transit states
--    in
--    epsilonClosure mappings $ flattenSet $ Data.Set.foldl union empty result
--    where   
--        transit state = (nddriver mappings) state alphabet

--collectStates mappings alphabets (old, new)
--    | emptied || reapeated  = collected
--    | otherwise             = collectStates mappings alphabets (collected, newTransisions)
--    where   transit state   = smap (\a -> epsilonTransition mappings state a) alphabets
--            newTransisions  = flattenSet $ smap transit new
--            collected       = union old new
--            emptied         = Data.Set.null newTransisions
--            reapeated       = newTransisions `isSubsetOf` old


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