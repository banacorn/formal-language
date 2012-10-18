module Automaton.FA (
    
    automaton,
    automatonN,


    trimUnreachableStates,
    minimizeDFA,
    formalizeDFA,

    negateDFA,
    unionDFA,
    intersectionDFA,

    dfa2nfa,
    nfa2dfa,

    -- NFA
    epsilonClosure,
    formalizeNFA,

) where

--------------------------------------------------------------

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
driverN :: Map -> NDTransition
driverN (NDMap mappings) state alphabet = 
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
dfa2nfa (DFA s a (Map mappings) i f) = (NFA s a (NDMap ndmappings) i f)
    where   ndmappings = fmap mapping2ndmapping mappings
            mapping2ndmapping (state, alphabet, target) = (state, alphabet, [target])

-- transform FFA to DFA
--nfa2dfa :: NFA -> DFA
nfa2dfa nfa = 4
    --states
    ----DFA sta alphabets mappings startN acceptsN
    --where
    --    NFA statesN alphabets mappingsN startN acceptsN = formalizeNFA nfa

    --    start = epsilonClosure mappingsN startN
    --    states = collectState mappingsN alphabets ([], start)


-- negation on FA
negateDFA :: DFA -> DFA
negateDFA (DFA states a m s accepts) = DFA states a m s (states \\ accepts)
negateNFA :: NFA -> NFA
negateNFA (NFA states a m s accepts) = NFA states a m s (states \\ accepts)


unionDFA :: DFA -> DFA -> DFA
unionDFA dfa0 dfa1 =
    DFA states alphabets mappings start accepts
    where
        DFA states0 alphabets mappings0 start0 accepts0 = formalizeDFA $ trimUnreachableStates dfa0
        DFA states1 _ mappings1 start1 accepts1 = formalizeDFA $ trimUnreachableStates dfa1

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
        DFA states0 alphabets mappings0 start0 accepts0 = formalizeDFA $ trimUnreachableStates dfa0
        DFA states1 _ mappings1 start1 accepts1 = formalizeDFA $ trimUnreachableStates dfa1

        stateSpace = length states0 * length states1
        encode = encodePair $ length states1
        driver0 = driver mappings0
        driver1 = driver mappings1

        states = [0 .. stateSpace - 1]
        mappings = Map $ triple <$> alphabets <*> states0 <*> states1
            where   triple a s0 s1 = (encode (s0, s1), a, encode (driver0 s0 a, driver1 s1 a))
        start = encode (start0, start1)
        accepts = curry encode <$> accepts0 <*> accepts1

-- helper functions
formalizeDFA :: DFA -> DFA
formalizeDFA (DFA states alphabets (Map mappings) start accepts) = 
    DFA states' alphabets (Map mappings') start' accepts'
    where   states' = [0 .. length states - 1]
            mappings' = nub $ map (\ (s, a, f) -> (replace s, a, replace f)) mappings
            start' = replace start
            accepts' = nub $ map replace accepts
            replace x = case elemIndex x states of Just a -> a
                                                   Nothing -> 0

formalizeNFA :: NFA -> NFA
formalizeNFA (NFA states alphabets (NDMap mappings) start accepts) = 
    NFA states' alphabets (NDMap mappings') start' accepts'
    where   states' = [0 .. length states - 1]
            mappings' = nub $ map (\ (s, a, f) -> (replace s, a, replace <$> f)) mappings
            start' = replace start
            accepts' = nub $ map replace accepts
            replace x = case elemIndex x states of Just a -> a
                                                   Nothing -> 0

encodePair size (a, b) = a * size + b




minimizeDFA dfa =
    (DFA states' alphabets (Map mappings') start' accepts')
    --formalize (DFA states' alphabets (Map mappings') start' accepts')
    where   -- input
            (DFA states alphabets (Map mappings) start accepts) = trimUnreachableStates dfa
            -- init data
            distinguished = accepts >>= de combinations
            mixed = combinations \\ distinguished
            -- helpers
            transit state = driver (Map mappings) state <$> alphabets
            de list state = filter (\ (a, b) -> a == state || b == state) list
            combinations = filter (uncurry (<)) $ curry id <$> states <*> states
            transitPair (a, b) = tweak <$> pairs
                where   pairs = uncurry zip (transit b, transit a)
                        tweak (a, b) = if a < b then (a, b) else (b, a)
            has target test = (flip elem test) <$> target
            partition mixed distinguished
                | null newDistinguished = mixed
                | otherwise = partition mixed' distinguished'
                where   distinguishableList = or <$> has distinguished <$> transitPair <$> mixed
                        newDistinguished = map fst $ filter snd $ zip mixed distinguishableList
                        distinguished' = union distinguished newDistinguished
                        mixed' = mixed \\ newDistinguished
            sameStates = partition mixed distinguished

            states' = nub $ replace <$> states
            mappings' = nub $ replaceMapping <$> mappings
            start' = replace start
            accepts' = nub $ replace <$> accepts

            replace state = case lookup state sameStates of Just new -> new
                                                            Nothing -> state
            replaceMapping (s, a, t) = (replace s, a, replace t)


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
            next states = (\ alphabet -> states >>= bana alphabet) <$> alphabets
            start' = return $ closure start 
            closure state = epsilonClosure mappings state


collect :: Eq a => (a -> [a]) -> ([a], [a]) -> [a]
collect next (old, new)
    | emptied   = old
    | reapeated = old
    | otherwise = collect next (old', new')
    where   new' = old >>= next
            old' = nub (old `union` new)
            emptied = null new'
            reapeated = new' `subsetOf` old
            subsetOf elems list = and (flip elem list <$> elems)








