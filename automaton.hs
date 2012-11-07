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
    renameStatesDFA,
    renameStatesNFA,



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
