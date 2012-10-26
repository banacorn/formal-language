module Automaton.FA (
    
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

import Automaton.Type

import Data.Bits (testBit)
import Control.Applicative hiding (empty)
import Control.Monad
import Data.List
--import qualified Data.IntMap as IntMap


--------------------------------------------------------------

-- make mappings a function
driver :: Map -> Transition
driver (Map mappings) state alphabet =
    let result = [ f | (s, a, f) <- mappings, s == state, a == alphabet ] in
    case result of [] -> error $ show state ++ ", " ++ show alphabet ++ " Transition not deinfed"
                   (x:xs) -> x

-- make mappings a function
driverN :: Map -> NDTransition
driverN (MapN mappings) state alphabet = 
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

automatonN :: NFA -> Language -> Bool
automatonN (NFA states alphabets mappings state accepts) [] = or $ closure state >>= accept
    where   closure state = epsilonClosure mappings state
            accept state = return $ elem state accepts

automatonN (NFA states alphabets mappings state accepts) language
    | head language `notElem` alphabets = False
    | otherwise = or $ consume language state
    where   closure state = epsilonClosure mappings state
            jump x state = driverN mappings state x
            accept state = return $ elem state accepts
            consume [] state = closure state >>= accept
            consume (x:xs) state = closure state >>= jump x >>= consume xs

epsilonClosure :: Map -> State -> States
epsilonClosure mappings state = nub . insert state . join $ epsilonClosure mappings <$> transit state ' '
    where   transit = driverN mappings

--epsilonTransition


----------------------------------------------------------------------
-- proofs
-- transform DFA to NFA
dfa2nfa :: DFA -> NFA
dfa2nfa (DFA s a (Map mappings) i f) = (NFA s a (MapN ndmappings) i f)
    where   ndmappings = fmap mapping2ndmapping mappings
            mapping2ndmapping (state, alphabet, target) = (state, alphabet, [target])




encodePowerset :: States -> State
encodePowerset = sum . fmap ((^) 2)
decodePowerset :: State -> States
decodePowerset = elemIndices 1 . bits 
    where   bits 0 = [0]
            bits 1 = [1]
            bits n = (mod n 2) : bits (div n 2)

ofPowerset e n = testBit n e


-- transform FFA to DFA
nfa2dfa :: NFA -> DFA
nfa2dfa nfa =
    formalizeDFA $ DFA states' alphabets (Map mappings') start' accepts'
    where
        NFA statesN alphabets mappingsN startN acceptsN = formalizeNFA nfa
        transit = driverN mappingsN

        start = epsilonClosure mappingsN startN
        states = collectStates mappingsN alphabets startN
        mappings = [ ( state, alphabet, nub $ join ( (flip transit alphabet) <$> state) >>=  epsilonClosure mappingsN ) | state <- states, alphabet <- alphabets ]
        accepts = filter acceptable states
            where acceptable = any (flip elem acceptsN)

        states' = encodePowerset <$> states
        mappings' = encodeMapping <$> mappings
            where encodeMapping (s, a, t) = (encodePowerset s, a, encodePowerset t)
        start' = encodePowerset start
        accepts' = encodePowerset <$> accepts

-- negation on FA
negateDFA :: DFA -> DFA
negateDFA (DFA states a m s accepts) = DFA states a m s (states \\ accepts)
negateNFA :: NFA -> NFA
negateNFA (NFA states a m s accepts) = NFA states a m s (states \\ accepts)


unionDFA :: DFA -> DFA -> DFA
unionDFA dfa0 dfa1 =
    DFA states alphabets mappings start accepts
    where
        DFA states0 alphabets (Map mappings0) start0 accepts0 = formalizeDFA dfa0
        DFA states1 _         (Map mappings1) start1 accepts1 = formalizeDFA dfa1

        stateSpace = length states0 * length states1
        encode (a, b) = a * length states1 + b

        states = [0 .. stateSpace - 1]
        mappings = Map [ (encode (s0, s1), a0, encode (t0, t1)) | (s0, a0, t0) <- mappings0, (s1, a1, t1) <- mappings1, a0 == a1]
        start = encode (start0, start1)
        accepts = [ encode (s0, s1) | s0 <- states0, s1 <- states1, elem s0 accepts0 || elem s1 accepts1 ]




intersectDFA :: DFA -> DFA -> DFA
intersectDFA dfa0 dfa1 =
    DFA states alphabets mappings start accepts
    where
        DFA states0 alphabets (Map mappings0) start0 accepts0 = formalizeDFA dfa0
        DFA states1 _         (Map mappings1) start1 accepts1 = formalizeDFA dfa1

        stateSpace = length states0 * length states1
        encode (a, b) = a * length states1 + b

        states = [0 .. stateSpace - 1]
        mappings = Map [ (encode (s0, s1), a0, encode (t0, t1)) | (s0, a0, t0) <- mappings0, (s1, a1, t1) <- mappings1, a0 == a1]
        start = encode (start0, start1)
        accepts = curry encode <$> accepts0 <*> accepts1

concatenateDFA :: DFA -> DFA -> DFA
concatenateDFA dfa0 dfa1 = minimizeDFA . formalizeDFA . nfa2dfa $ nfa0 `concatenateNFA` nfa1
    where 
        nfa0 = dfa2nfa dfa0
        nfa1 = dfa2nfa dfa1

-- helper functions
formalizeDFA :: DFA -> DFA
formalizeDFA dfa = replaceStatesDFA function dfa
    where   getStates (DFA s _ _ _ _) = s
            table = zip (getStates dfa) [0..]
            function s = case lookup s table of Just a -> a
                                                Nothing -> 0

formalizeNFA :: NFA -> NFA
formalizeNFA nfa = replaceStatesNFA function nfa
    where   getStates (NFA s _ _ _ _) = s
            table = zip (getStates nfa) [0..]
            function s = case lookup s table of Just a -> a
                                                Nothing -> 0


minimizeDFA dfa = replaceStatesDFA replace dfa
    where   undistinguishablePairs = undistinguishableStates dfa
            replace a = case lookup a undistinguishablePairs of
                Just b  -> b
                Nothing -> a

undistinguishableStates dfa = 
    combinations \\ collect' distinguishable (initialDisguindished, initialMixed)
    where
        (DFA states alphabets (Map mappings) start accepts) = dfa

        combinations = filter (uncurry (<)) $ curry id <$> states <*> states
        initialDisguindished = filter distinguishable combinations
            where distinguishable (a, b) = a `elem` accepts || b `elem` accepts
        initialMixed = combinations \\ initialDisguindished

        transitPair pair = jump pair <$> alphabets
        jump (a, b) alphabet = (driver (Map mappings) a alphabet, driver (Map mappings) b alphabet)

        distinguishable distinguished pair =
            case or result of 
                True -> [pair]
                False -> []
            where   sort (a, b) = if a < b then (a, b) else (b, a)
                    check (a, b) = (a, b) `elem` distinguished && a /= b
                    result = check . sort <$> transitPair pair

trimUnreachableStates :: DFA -> DFA
trimUnreachableStates (DFA states alphabets (Map mappings) start accepts) = 
    (DFA states' alphabets (Map mappings') start accepts')
    where   states' = collectState (Map mappings) alphabets start
            trimmedStates = states \\ states'
            mappings' = filter (reachable states') mappings
                where reachable states (a, b, c) = elem a states && elem c states
            accepts' = accepts \\ trimmedStates

collectState :: Map -> Alphabets -> State -> States
collectState mappings alphabets start = collect next ([start], [start])
    where next state = driver mappings state <$> alphabets

collectStates :: Map -> Alphabets -> State -> [States]
collectStates mappings alphabets start = collect next (start', start')
    where   bana alphabet state = driverN mappings state alphabet >>= closure
            next states = (\ alphabet -> nub . sort $ states >>= bana alphabet) <$> alphabets
            start' = return $ closure start 
            closure state = epsilonClosure mappings state


collect :: Eq a => (a -> [a]) -> ([a], [a]) -> [a]
collect next (old, new)
    | emptied   = old
    | reapeated = old
    | otherwise = nub $ collect next (old', new')
    where   new' = old >>= next
            old' = nub (old `union` new)
            emptied = null new'
            reapeated = new' `subsetOf` old
            subsetOf elems list = and (flip elem list <$> elems)


collect' :: Eq a => ([a] -> a -> [a]) -> ([a], [a]) -> [a]
collect' process (collected, raw)
    | emptied   = collected
    | reapeated = collected
    | otherwise = nub $ collect' process (collected', raw')
    where   processed = raw >>= process collected
            collected' = nub (collected `union` processed)
            raw' = raw \\ processed
            emptied = null raw'
            reapeated = raw `subsetOf` raw'
            subsetOf elems list = and (flip elem list <$> elems)

----------------------------------------------------------------------

unionNFA :: NFA -> NFA -> NFA
unionNFA nfa0 nfa1 =
    NFA states alphabets mappings start accepts
    where
        NFA states0 alphabets (MapN mappings0) start0 accepts0 = formalizeNFA nfa0
        NFA states1 _ (MapN mappings1) start1 accepts1 = replace nfa1
        
        replace = replaceStatesNFA ((+) $ length states0)
        start = maximum states1 + 1

        states = start `insert` (states0 `union` states1)
        mappings = MapN $ mappings0 `union` mappings1 `union` [(start, ' ', [start0, start1])]
        accepts = accepts0 `union` accepts1

intersectNFA :: NFA -> NFA -> NFA
intersectNFA nfa0 nfa1 = dfa2nfa dfaIntersection
    where   dfa0 = nfa2dfa nfa0
            dfa1 = nfa2dfa nfa1
            dfaIntersection = minimizeDFA $ dfa0 `intersectDFA` dfa1

concatenateNFA :: NFA -> NFA -> NFA
concatenateNFA nfa0 nfa1 =
    formalizeNFA (NFA states alphabets (MapN mappings) start0 accepts1)
    where
        (NFA states0 alphabets (MapN mappings0) start0 accepts0) = nfa0
        (NFA states1 _         (MapN mappings1) start1 accepts1) = replace nfa1

        offset = maximum states0 - minimum states0 + 1
        replace = replaceStatesNFA (+ offset)

        end = [ (s, ' ', t) | (s, a, t) <- mappings0, s `elem` accepts0, a == ' ' ]
        mappings = case end of []        -> bridge `union` mappings0 `union` mappings1
                               otherwise -> bridge' `union` (mappings0 \\ end) `union` mappings1
            where   bridge = [ (s, ' ', [start1]) | s <- accepts0 ]
                    bridge' = [ (s, a, start1 `insert` ts) | (s, a, ts) <- end ]
        
        states = states0 `union` states1



statesMin = [0..7]
alphabetsMin = ['0', '1']

mappingsMin = Map [
    (0, '0', 1),
    (0, '1', 5),
    (1, '0', 6),
    (1, '1', 2),
    (2, '0', 0),
    (2, '1', 2),
    (3, '0', 2),
    (3, '1', 6),
    (4, '0', 7),
    (4, '1', 5),
    (5, '0', 2),
    (5, '1', 6),
    (6, '0', 6),
    (6, '1', 4),
    (7, '0', 6),
    (7, '1', 2)
    ]

startMin = 0
acceptsMin = [2]
dfaMin = DFA statesMin alphabetsMin mappingsMin startMin acceptsMin

----

replaceStatesDFA :: (State -> State) -> DFA -> DFA
replaceStatesDFA table (DFA states alphabets (Map mappings) start accepts) = 
    DFA states' alphabets (Map mappings') start' accepts'
    where   states'     = nub $ table <$> states
            mappings'   = nub $ replaceMapping <$> mappings
                where replaceMapping (s, a, t) = (table s, a, table t)
            start'      = table start
            accepts'    = nub $ table <$> accepts



replaceStatesNFA :: (State -> State) -> NFA -> NFA
replaceStatesNFA table (NFA states alphabets (MapN mappings) start accepts) = 
    NFA states' alphabets (MapN mappings') start' accepts'
    where   states'     = nub $ table <$> states
            mappings'   = nub $ replaceMapping <$> mappings
                where replaceMapping (s, a, t) = (table s, a, table <$> t)
            start'      = table start
            accepts'    = nub $ table <$> accepts

