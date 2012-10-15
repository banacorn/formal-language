module Automaton (
    
    -- types

    State,
    States,
    Alphabet,
    Alphabets,
    Language,
    Map(..),
    DFA(..),
    NFA(..),

    -- functions

    automaton,
    automatonN,

    negateDFA,
    unionDFA,
    intersectionDFA



) where

--------------------------------------------------------------

import Automaton.Instances
import Automaton.Type

import Data.Bits (testBit)
import Control.Applicative hiding (empty)
import Control.Monad
import Data.List


--------------------------------------------------------------

-- make mappings a function
driver :: Map -> Transition
driver (Map mappings) state alphabet =
    let result = [ f | (s, a, f) <- mappings, s == state, a == alphabet ] in
    case result of [] -> error $ show state ++ ", " ++ show alphabet ++ " Transition not deinfed"
                   (x:xs) -> x

-- make mappings a function
nddriver :: Map -> NDTransition
nddriver (NDMap mappings) state alphabet = 
    let result = [ f | (s, a, f) <- mappings, s == state, a == alphabet ] in
    case result of [] -> []
                   (x:xs) -> x

-- the automaton
automaton :: DFA -> Language -> Bool
automaton (DFA states alphabets mappings state accepts) [] = elem state accepts
automaton (DFA states alphabets mappings state accepts) (x:xs)
    | notElem x alphabets = False
    | otherwise = automaton (DFA states alphabets mappings nextState accepts) xs
    where   nextState = (driver mappings) state x


automatonN (NFA states alphabets mappings state accepts) [] = or [accepted, epsilon]
    where   accepted = elem state accepts 
            epsilon  = or . map (flip elem accepts) $ (nddriver mappings) state ' '

automatonN (NFA states alphabets mappings state accepts) (x:xs)
    | not . null $ transit state ' ' = True
    | notElem x alphabets = False
    | otherwise = or $ map (\next -> automatonN (NFA states alphabets mappings next accepts) xs ) nextState
    where   
        transit     = nddriver mappings
        nextState   = union alphabet epsilon
        alphabet    = transit state x
        epsilon     = transit state ' '
        extendedAlphabets = insert ' ' alphabets

states = [0..1]
alphabets = ['a' .. 'b']

mappings = Map [
    (0, 'b', 1),
    (0, 'a', 0),
    (1, 'b', 1),
    (1, 'a', 0)
    ]


ndmappings = NDMap [
    (0, ' ', [2]),
    (0, 'a', [1]),
    (1, 'b', [1, 3]),
    (2, ' ', [1]),
    (2, 'a', [3]),
    (3, 'a', [2])
    ]

start = 0
accepts = [2]



statesA = [2..3]
mappingsA = Map [
    (2, 'b', 3),
    (2, 'a', 2),
    (3, 'b', 3),
    (3, 'a', 3)
    ]

startA = 2
acceptsA = [3]



nfa = NFA states alphabets ndmappings start accepts
dfa = DFA states alphabets mappings start accepts
dfaa = DFA statesA alphabets mappingsA startA acceptsA

u = dfa `unionDFA` dfaa

----------------------------------------------------------------------
-- proofs



-- transform DFA to NFA
dfa2nfa :: DFA -> NFA
dfa2nfa (DFA s a (Map mappings) i f) = (NFA s a (NDMap ndmappings) i f)
    where   ndmappings = fmap mapping2ndmapping mappings
            mapping2ndmapping (state, alphabet, target) = (state, alphabet, [target])



-- negation on FA
negateDFA :: DFA -> DFA
negateDFA (DFA states a m s accepts) = DFA states a m s (states \\ accepts)
negateNFA :: NFA -> NFA
negateNFA (NFA states a m s accepts) = NFA states a m s (states \\ accepts)


unionDFA :: DFA -> DFA -> DFA
unionDFA dfa0 dfa1 =
    DFA states alphabets mappings start accepts
    where
        DFA states0 alphabets mappings0 start0 accepts0 = formalize dfa0
        DFA states1 _ mappings1 start1 accepts1 = formalize dfa1

        stateSpace = length states0 * length states1
        encode = encodePair $ length states1
        driver0 = driver mappings0
        driver1 = driver mappings1
        states = [0 .. stateSpace - 1]
        mappings = Map $ triple <$> alphabets <*> states0 <*> states1
            where   triple a s0 s1 = (encode (s0, s1), a, encode (driver0 s0 a, driver1 s1 a))
        start = encode (start0, start1)
        accepts = [ encode (s0, s1) | s0 <- states0, s1 <- states1, elem s0 accepts0 || elem s1 accepts1 ]



intersectionDFA :: DFA -> DFA -> DFA
intersectionDFA dfa0 dfa1 =
    DFA states alphabets mappings start accepts
    where
        DFA states0 alphabets mappings0 start0 accepts0 = formalize dfa0
        DFA states1 _ mappings1 start1 accepts1 = formalize dfa1

        stateSpace = length states0 * length states1
        encode = encodePair $ length states1
        driver0 = driver mappings0
        driver1 = driver mappings1

        states = [0 .. stateSpace - 1]
        mappings = Map [ (encode (s0, s1), a, encode (driver0 s0 a, driver1 s1 a)) | a <- alphabets , s0 <- states0, s1 <- states1 ]
        start = encode (start0, start1)
        accepts = [ encode (a0, a1) | a0 <- accepts0, a1 <- accepts1 ]

-- helper functions
formalize :: DFA -> DFA
formalize (DFA states alphabets (Map mappings) start accepts) = 
    DFA states' alphabets (Map mappings') start' accepts'
    where   states' = [0 .. length states - 1]
            mappings' = map (\ (s, a, f) -> (replace s, a, replace f)) mappings
            start' = replace start
            accepts' = map replace accepts
            replace x = case elemIndex x states of Just a -> a
                                                   Nothing -> 0

encodePair size (a, b) = a * size + b

--encodePair' :: (Eq a1, Eq a) => (Set a, Set a1) -> (a, a1) -> State
--encodePair' (setA, setB) (a, b) = index
--    where   listA = toList setA
--            listB = toList setB
--            indexA = List.elemIndex a listA
--            indexB = List.elemIndex b listB
--            base = fmap (* size setB) indexA 
--            index = case (+) <$> base <*> indexB of Just a -> a
--                                                    Nothing -> 0

--tq = fromList [0 .. 3]
--ta = fromList [0, 2, 3]

--encodePowerset :: States -> State
--encodePowerset = sum . fmap ((^) 2) . toList
--decodePowerset :: State -> States
--decodePowerset = fromList . List.elemIndices 1 . bits 
--    where   bits 0 = [0]
--            bits 1 = [1]
--            bits n = (mod n 2) : bits (div n 2)
--ofPowerset e n = testBit n e




----nfa2dfa :: (Ord a) => FA a -> FA a
----nfa2dfa nfa = 
----    DFA' states alphabets mappings' start' accepts
----    where
----        NFA ndstates alphabets ndmappings ndstart ndaccepts = formalize nfa

----        transit =  ndmappings
----        start = epsilonClosure ndmappings ndstart
----        states = collectStates ndmappings alphabets (empty, singleton start)
----        mappings' = Map [ ( state, alphabet,  flattenSet $  smap (flip transit alphabet) state ) | state <- toList states, alphabet <- toList alphabets ]
----        start' =  start
----        states' = smap encodePowerset states
----        --accepts = Data.Set.filter (\ state -> and . toList $ smap (flip ofPowerset state) ndaccepts ) states'
----        accepts = Data.Set.filter (\ state -> and . toList $ smap (flip member state) ndaccepts ) states

----t = nfa2dfa nfa

--flattenSet :: (Ord a) => Set (Set a) -> Set a
--flattenSet setset = Data.Set.foldl union empty setset

--epsilonClosure :: Map -> State -> States
--epsilonClosure mappings state = insert state $ flattenSet $ smap (epsilonClosure mappings) (transit state ' ')
--    where   transit = nddriver mappings


--epsilonTransition :: Map -> State -> Alphabet -> States
--epsilonTransition mappings state alphabet =
--    let 
--        states = epsilonClosure mappings state 
--        result = smap transit states
--    in
--    flattenSet $ smap (epsilonClosure mappings) (Data.Set.foldl union empty result)
--    where
--        transit state = (nddriver mappings) state alphabet

--collectStates :: Map -> Alphabets -> (Set States, Set States) -> Set States
--collectStates mappings alphabets (old, new)
--    | emptied || reapeated  = collected
--    | otherwise             = collectStates mappings alphabets (collected, newTransisions)
--    where   transit states   = smap (\a -> smap (\state -> epsilonTransition mappings state a) states) alphabets
--            newTransisions  = flattenSet . flattenSet $ smap transit new
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