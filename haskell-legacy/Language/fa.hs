module Language.FA (
    
    driverDFA,
    driverNFA,


    trimUnreachableStates,
    minimizeDFA,
    replaceStatesDFA,
    replaceStatesNFA,
    nubStatesDFA,
    nubStatesNFA,
    collectState,
    collectStates,
    collect,

    dfa2nfa,
    nfa2dfa,

    -- NFA
    epsilonClosure,

    undistinguishableStates,

) where

--------------------------------------------------------------

import Prelude hiding (negate)
import Automaton.Type
import Automaton.Util

import Data.Bits (testBit)
import Control.Applicative hiding (empty)
import Control.Monad
import qualified Data.List as List
--import qualified Data.List as List (union, intersect)
import Debug.Trace


--------------------------------------------------------------


-- instance of Automaton
instance Automaton DFA where
    automaton (DFA states alphabets mappings state []) _ = False
    automaton (DFA states alphabets mappings state accepts) [] = elem state accepts
    automaton (DFA states alphabets mappings state accepts) (x:xs)
        | notElem (Alphabet x) alphabets = False
        | otherwise = automaton (DFA states alphabets mappings nextState accepts) xs
        where   nextState = (driverDFA mappings) state (Alphabet x)

    -- nub and replace states with natural numbers (states not minimized!!)
    normalize dfa = replaceStatesDFA function . nubStatesDFA $ dfa
        where   getStates (DFA states _ _ _ _) = states
                table = zip (getStates dfa) [0..]
                function s = case lookup s table of Just a -> a
                                                    Nothing -> 0

instance Automaton NFA where
    automaton (NFA states alphabets mappings state []) _ = False
    automaton (NFA states alphabets mappings state accepts) [] = (state `elem` accepts) || (or $ closure state >>= accept)
        where   closure state = epsilonClosure mappings state
                accept state = return $ elem state accepts
    automaton (NFA states alphabets mappings state accepts) language
        | (Alphabet (head language)) `notElem` alphabets = False
        | otherwise = or $ consume language state
        where   closure state = epsilonClosure mappings state
                jump x state = driverNFA mappings state x
                accept state = return $ elem state accepts
                consume [] state = closure state >>= accept
                consume (x:xs) state = closure state >>= jump (Alphabet x) >>= consume xs

    normalize nfa = replaceStatesNFA function . nubStatesNFA $ nfa
        where   getStates (NFA s _ _ _ _) = s
                table = zip (getStates nfa) [0..]
                function s = case lookup s table of Just a -> a
                                                    Nothing -> 0


----------------------------------------------------------------------



----------------------------
--
--  DFA <=> NFA
--
----------------------------


dfa2nfa :: DFA -> NFA
dfa2nfa (DFA s a (TransitionsDFA mappings) i f) = (NFA s a (TransitionsNFA ndmappings) i f)
    where   ndmappings = mapping2ndmapping <$> mappings
            mapping2ndmapping (state, alphabet, target) = (state, alphabet, [target])


nfa2dfa :: NFA -> DFA
nfa2dfa nfa =
    nubStatesDFA $ DFA states' alphabets (TransitionsDFA mappings') start' accepts'
    where
        NFA statesN alphabets mappingsN startN acceptsN = normalize nfa
        transit = driverNFA mappingsN

        start = epsilonClosure mappingsN startN
        states = collectStates mappingsN alphabets startN
        mappings = [ ( state, alphabet, List.nub $ join ( (flip transit alphabet) <$> state) >>=  epsilonClosure mappingsN ) | state <- states, alphabet <- alphabets ]
        accepts = filter acceptable states
            where acceptable = any (flip elem acceptsN)

        states' = encodePowerset <$> states
        mappings' = encodeMapping <$> mappings
            where encodeMapping (s, a, t) = (encodePowerset s, a, encodePowerset t)
        start' = encodePowerset start
        accepts' = encodePowerset <$> accepts


----------------------------
--
--  Negation
--
----------------------------

instance FiniteAutomaton DFA where
    negate (DFA states a m s accepts) = DFA states a m s (states List.\\ accepts)

    union dfa0 dfa1 =
            DFA states alphabets mappings start accepts
            where
                DFA states0 alphabets (TransitionsDFA mappings0) start0 accepts0 = normalize dfa0
                DFA states1 _         (TransitionsDFA mappings1) start1 accepts1 = normalize dfa1

                stateSpace = length states0 * length states1
                encode (a, b) = a * length states1 + b

                states = [0 .. stateSpace - 1]
                mappings = TransitionsDFA [ (encode (s0, s1), a0, encode (t0, t1)) | (s0, a0, t0) <- mappings0, (s1, a1, t1) <- mappings1, a0 == a1]
                start = encode (start0, start1)
                accepts = [ encode (s0, s1) | s0 <- states0, s1 <- states1, elem s0 accepts0 || elem s1 accepts1 ]

    intersect dfa0 dfa1 = DFA states alphabets mappings start accepts
        where
            DFA states0 alphabets (TransitionsDFA mappings0) start0 accepts0 = normalize dfa0
            DFA states1 _         (TransitionsDFA mappings1) start1 accepts1 = normalize dfa1

            stateSpace = length states0 * length states1
            encode (a, b) = a * length states1 + b

            states = [0 .. stateSpace - 1]
            mappings = TransitionsDFA [ (encode (s0, s1), a0, encode (t0, t1)) | (s0, a0, t0) <- mappings0, (s1, a1, t1) <- mappings1, a0 == a1]
            start = encode (start0, start1)
            accepts = curry encode <$> accepts0 <*> accepts1

    concatenate dfa0 dfa1 = minimizeDFA . normalize . nfa2dfa $ nfa0 `concatenate` nfa1
        where 
            nfa0 = dfa2nfa dfa0
            nfa1 = dfa2nfa dfa1

    kleeneStar = nfa2dfa . kleeneStar . dfa2nfa



instance FiniteAutomaton NFA where
    negate = dfa2nfa . negate . nfa2dfa

    union nfa0 nfa1 =
        NFA states alphabets mappings start accepts
        where
            NFA states0 alphabets (TransitionsNFA mappings0) start0 accepts0 = normalize nfa0
            NFA states1 _ (TransitionsNFA mappings1) start1 accepts1 = replace nfa1
            
            replace = replaceStatesNFA ((+) $ length states0)
            start = maximum states1 + 1

            states = start `List.insert` (states0 `List.union` states1)
            mappings = TransitionsNFA $ mappings0 `List.union` mappings1 `List.union` [(start, Epsilon, [start0, start1])]
            accepts = accepts0 `List.union` accepts1

    intersect nfa0 nfa1 = dfa2nfa dfaIntersection
        where   dfa0 = nfa2dfa nfa0
                dfa1 = nfa2dfa nfa1
                dfaIntersection = minimizeDFA $ dfa0 `intersect` dfa1

    concatenate nfa0 nfa1 =
        normalize (NFA states alphabets (TransitionsNFA mappings) start0 accepts1)
        where
            (NFA states0 alphabets (TransitionsNFA mappings0) start0 accepts0) = nfa0
            (NFA states1 _         (TransitionsNFA mappings1) start1 accepts1) = replace nfa1

            offset = maximum states0 - minimum states0 + 1
            replace = replaceStatesNFA (+ offset)

            end = [ (s, Epsilon, t) | (s, a, t) <- mappings0, s `elem` accepts0, a == Epsilon ]
            mappings = case end of []        -> bridge `List.union` mappings0 `List.union` mappings1
                                   otherwise -> bridge' `List.union` (mappings0 List.\\ end) `List.union` mappings1
                where   bridge = [ (s, Epsilon, [start1]) | s <- accepts0 ]
                        bridge' = [ (s, a, start1 `List.insert` ts) | (s, a, ts) <- end ]
            
            states = states0 `List.union` states1

    kleeneStar (NFA states alphabets (TransitionsNFA mappings) start accepts) =
        normalize (NFA states' alphabets (TransitionsNFA mappings') start' accepts')
        where
            start' = maximum states + 1
            states' = start' `List.insert` states
            accepts' = start' `List.insert` accepts
            mappings' = mappings ++ (backToTheStart <$> (start':accepts))

            backToTheStart state = (state, Epsilon, [start])


----------------------------
--
--  Helper Functions
--
----------------------------


encodePowerset :: States -> State
encodePowerset = sum . fmap ((^) 2)


-- replace states with given SURJECTIVE function
replaceStatesDFA :: (State -> State) -> DFA -> DFA
replaceStatesDFA table (DFA states alphabets (TransitionsDFA mappings) start accepts) = 
    DFA states' alphabets (TransitionsDFA mappings') start' accepts'
    where   states'     = table <$> states
            mappings'   = replaceMapping <$> mappings
                where replaceMapping (s, a, t) = (table s, a, table t)
            start'      = table start
            accepts'    = table <$> accepts



replaceStatesNFA :: (State -> State) -> NFA -> NFA
replaceStatesNFA table (NFA states alphabets (TransitionsNFA mappings) start accepts) = 
    NFA states' alphabets (TransitionsNFA mappings') start' accepts'
    where   states'     = table <$> states
            mappings'   = replaceMapping <$> mappings
                where replaceMapping (s, a, t) = (table s, a, table <$> t)
            start'      = table start
            accepts'    = table <$> accepts

-- nub the states
nubStatesDFA :: DFA -> DFA
nubStatesDFA (DFA states alphabets (TransitionsDFA mappings) start accepts) = 
    DFA states' alphabets (TransitionsDFA mappings') start accepts'
    where   states' = List.nub states
            mappings' = List.nub mappings
            accepts' = List.nub accepts

nubStatesNFA :: NFA -> NFA
nubStatesNFA (NFA states alphabets (TransitionsNFA mappings) start accepts) = 
    NFA states' alphabets (TransitionsNFA mappings') start accepts'
    where   states' = List.nub states
            mappings' = filter validTransition $ glue <$> (List.groupBy sameMapping $ List.sort mappings)
            accepts' = List.nub accepts

            validTransition (_, _, []) = False
            validTransition (_, _, _) = True

            sameMapping (s, a, t) (s', a', t') = s == s' && a == a'
            glue mappings = case glue' mappings $ head mappings of
                (s, Epsilon, ts) -> (s, Epsilon, List.delete s (List.nub ts))
                (s, a, ts) -> (s, a, List.nub ts)
            glue' [] result = result
            glue' ((_, _, t):rest) (s, a, ts) = glue' rest (s, a, t ++ ts) 




minimizeDFA :: DFA -> DFA
minimizeDFA dfa = nubStatesDFA $ replaceStatesDFA replace dfa
    where   undistinguishablePairs = undistinguishableStates dfa
            replace a = case lookup a undistinguishablePairs of
                Just b  -> b
                Nothing -> a

undistinguishableStates :: DFA -> [(State, State)]
undistinguishableStates dfa = 
    combinations List.\\ collect' (distinguishable dfa) (initialDisguindished, initialMixed)
    where
        (DFA states alphabets (TransitionsDFA mappings) start accepts) = dfa

        combinations = pairCombinations states
        initialDisguindished = filter distinguishable combinations
            where distinguishable (a, b) = (a `elem` accepts && b `notElem` accepts) || (a `notElem` accepts && b `elem` accepts)
        initialMixed = combinations List.\\ initialDisguindished


distinguishable :: DFA -> [(State, State)] -> (State, State) -> [(State, State)]
distinguishable dfa distinguished pair = 
    case or result of 
        True -> [pair]
        False -> []
    where   (DFA states alphabets (TransitionsDFA mappings) start accepts) = dfa
            
            transitPair pair = jump pair <$> alphabets
            jump (a, b) alphabet = (driverDFA (TransitionsDFA mappings) a alphabet, driverDFA (TransitionsDFA mappings) b alphabet)

            sort (a, b) = if a < b then (a, b) else (b, a)
            check (a, b) = (a, b) `elem` distinguished && a /= b
            result = check . sort <$> transitPair pair




pairCombinations :: (Ord a) => [a] -> [(a, a)]
pairCombinations [] = []
pairCombinations (x:xs) = map (sort . curry id x) xs ++ pairCombinations xs
    where sort (a, b) = if a < b then (a, b) else (b, a)


trimUnreachableStates :: DFA -> DFA
trimUnreachableStates (DFA states alphabets (TransitionsDFA mappings) start accepts) = 
    (DFA states' alphabets (TransitionsDFA mappings') start accepts')
    where   states' = collectState (TransitionsDFA mappings) alphabets start
            trimmedStates = states List.\\ states'
            mappings' = filter (reachable states') mappings
                where reachable states (a, b, c) = elem a states && elem c states
            accepts' = accepts List.\\ trimmedStates

collectState :: Transitions -> Alphabets -> State -> States
collectState mappings alphabets start = collect next ([start], [start])
    where next state = driverDFA mappings state <$> alphabets

collectStates :: Transitions -> Alphabets -> State -> [States]
collectStates mappings alphabets start = collect next (start', start')
    where   bana alphabet state = driverNFA mappings state alphabet >>= closure
            next states = (\ alphabet -> List.nub . List.sort $ states >>= bana alphabet) <$> alphabets
            start' = return $ closure start 
            closure state = epsilonClosure mappings state

collect :: (Show a, Eq a) => (a -> [a]) -> ([a], [a]) -> [a]
collect next (old, new)
    | emptied   = old
    | reapeated = old
    | otherwise = (List.nub $ collect next (old', new'))
    where   new' = List.nub $ old >>= next
            old' = List.nub (old `List.union` new)
            emptied = null new'
            reapeated = new' `subsetOf` old
            subsetOf elems list = and (flip elem list <$> elems)



collect' :: (Show a, Eq a) => ([a] -> a -> [a]) -> ([a], [a]) -> [a]
collect' next (old, new)
    | emptied = old
    | reapeated = old
    | otherwise = List.nub $ collect' next (old', new')
    where   new' = List.nub $ new >>= next old
            old' = List.nub (old `List.union` new)
            emptied = null new'
            reapeated = new' `subsetOf` old
            subsetOf elems list = and (flip elem list <$> elems)


