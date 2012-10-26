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

    trimUnreachableStates,
    minimizeDFA,
    formalizeDFA,


    negateDFA,
    unionDFA,
    intersectDFA,
    concatenateDFA,


    dfa2nfa,
    nfa2dfa,


    -- NFA
    epsilonClosure,
    formalizeNFA,
    
    negateNFA,
    unionNFA,
    intersectNFA,
    concatenateNFA,

    undistinguishableStates


) where


--------------------------------------------------------------

import Automaton.Instances
import Automaton.Type
import Automaton.FA


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

--intersectFA :: (Ord a) => FA a -> FA a -> FA a
--intersectFA (DFA states0 alphabets0 transition0 (S start0) accepts0) (DFA states1 alphabets1 transition1 (S start1) accepts1) =
--    DFA states alphabets0 transition start accepts
--    where   states = states0 *. states1
--            transition (s0 :. S s1) a = next0 :. S next1
--                where   (S next0) = transition0 (S s0) a
--                        (S next1) = transition1 (S s1) a
--            start = start0 :. S start1
--            accepts = accepts0 *. accepts1