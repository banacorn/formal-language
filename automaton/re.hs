module Automaton.RE where

import Debug.Trace
import Automaton.Type
import Automaton.FA
import Data.List
import Control.Applicative


alphabetSet = Alphabet <$> ['0' .. '9'] ++ ['a' .. 'z'] ++ [' ']

re2nfa :: RE -> NFA
re2nfa (A a) = NFA states alphabets (MapN mappings) start accept 
    where   states = [0, 1]
            alphabets = [Alphabet a]
            mappings = [(0, Alphabet a, [1])]
            start = 0
            accept = [1]


re2nfa (E :+ a) = re2nfa a
re2nfa (a :+ E) = re2nfa a
re2nfa (a :+ b) = NFA states alphabets (MapN mappings) start accept
    where   NFA states0 alphabets0 (MapN mappings0) start0 accept0 = re2nfa a
            NFA states1 alphabets1 (MapN mappings1) start1 accept1 = replaceStatesNFA replaceStates $ re2nfa b

            states = states0 ++ states1
            alphabets = nub $ union alphabets0 alphabets1
            mappings = mappings0 ++ mappings1 ++ bridges
                where   bridges = [ (endpoint, Epsilon, [start1]) | endpoint <- accept0 ]

            start = start0
            accept = accept1

            replaceStates = (+) (maximum states0 + 1)


re2nfa (N :| a) = re2nfa a
re2nfa (a :| N) = re2nfa a
re2nfa (a :| b) = NFA states alphabets (MapN mappings) start accept
    where   NFA states0 alphabets0 (MapN mappings0) start0 accept0 = re2nfa a
            NFA states1 alphabets1 (MapN mappings1) start1 accept1 = replaceStatesNFA replaceStates $ re2nfa b

            start = maximum states1 + 1
            states = start : states0 ++ states1
            alphabets = nub $ union alphabets0 alphabets1

            mappings = (start, Epsilon, [start0, start1]) : mappings0 ++ mappings1

            accept = union accept0 accept1

            replaceStates = (+) (maximum states0 + 1)



re2nfa (Star a) = NFA states' alphabets (MapN mappings') start' accept'
    where   NFA states alphabets (MapN mappings) start accept = re2nfa a

            start' = maximum states + 1
            states' = start' : states
            accept' = start' : accept

            mappings' = mappings ++ bridges
                where   bridges = [ (endpoint, Epsilon, [start]) | endpoint <- accept' ]

re2nfa E = NFA [0] [Epsilon] (MapN [(0, Epsilon, [0])]) 0 [0]

re2nfa N = NFA [0] [] (MapN []) 0 []

--------

alphabet2re :: Alphabet -> RE
alphabet2re (Alphabet a) = A a
alphabet2re Epsilon = E

nfa2gnfa :: NFA -> GNFA
nfa2gnfa (NFA states alphabets (MapN mappings) start accept) =
    GNFA states' alphabets (MapRE mappings') start' accept'
    where
        start' = minimum states - 1
        accept' = [maximum states + 1]
        states' = start' : (accept' ++ states)
        mappings' = (\ from to ->
                case [ (from, alphabet2re a, to) | (s, a, t) <- extendedMappings, s == from, to `elem` t] of
                    []      -> (from, N, to)
                    triples -> (from, foldl1 (:|) (symbols triples), to)
            ) <$> domain <*> codomain
            
            where   second (_, a, _)    = a
                    symbols triples     = second <$> triples
                    startBridge         = (start', Epsilon, [start])
                    finalBridges        = (\f -> (f, Epsilon, accept')) <$> accept
                    extendedMappings    = startBridge : (mappings ++ finalBridges)
                    domain              = start' : states
                    codomain            = states ++ accept'


gnfa2re :: GNFA -> RE
gnfa2re (GNFA _ _ (MapRE []) _ _) = N
gnfa2re (GNFA _ _ (MapRE [(_, re, _)]) _ _) = re
gnfa2re (GNFA (x:xs) alphabets (MapRE mappings) start accept)
    | x == start        = gnfa2re (GNFA (xs ++ [x]) alphabets (MapRE mappings) start accept)
    | x `elem` accept   = gnfa2re (GNFA (xs ++ [x]) alphabets (MapRE mappings) start accept)
    | otherwise         = gnfa2re (GNFA (xs) alphabets (MapRE [(0, E, 1)]) start accept)




