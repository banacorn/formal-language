module Automaton.RE where

import Debug.Trace
import Automaton.Type
import Automaton.FA
import Data.List

alphabetSet = ['0' .. '9'] ++ ['a' .. 'z']

re2nfa :: RE -> NFA
re2nfa (A a) = NFA states alphabets (MapN mappings) start accept 
    where   states = [0, 1]
            alphabets = [a]
            mappings = [(0, a, [1])]
            start = 0
            accept = [1]


re2nfa (a :+ b) = NFA states alphabets (MapN mappings) start accept
    where   NFA states0 alphabets0 (MapN mappings0) start0 accept0 = re2nfa a
            NFA states1 alphabets1 (MapN mappings1) start1 accept1 = replaceStatesNFA replaceStates $ re2nfa b

            states = states0 ++ states1
            alphabets = nub $ union alphabets0 alphabets1
            mappings = mappings0 ++ mappings1 ++ bridges
                where   bridges = [ (endpoint, ' ', [start1]) | endpoint <- accept0 ]

            start = start0
            accept = accept1

            replaceStates = (+) (maximum states0 + 1)
