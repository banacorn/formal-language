module Automaton (
    
    -- types

    State,
    States,
    Alphabet(..),
    Alphabets,
    Language,
    Transitions(..),
    DFA(..),
    NFA(..),
    GNFA(..),

    RE(..),

    -- functions

    driver,
    driverN,
    automaton,
    automatonN,

    trimUnreachableStates,
    minimizeDFA,
    normalizeDFA,    
    replaceStatesDFA,
    replaceStatesNFA,
    nubStatesDFA,
    nubStatesNFA,
    collectState,
    collectStates,
    collect,



    negateDFA,
    unionDFA,
    intersectDFA,
    concatenateDFA,
    kleeneStarDFA,

    dfa2nfa,
    nfa2dfa,


    -- NFA
    epsilonClosure,
    normalizeNFA,
    
    negateNFA,
    unionNFA,
    intersectNFA,
    concatenateNFA,
    kleeneStarNFA,

    undistinguishableStates,

    -- RE
    re2nfa,
    nfa2gnfa,
    gnfa2re,
    alphabet2re,
    nfa2re,
    normalizeRE


) where


--------------------------------------------------------------

import Automaton.Instances
import Automaton.Type
import Automaton.FA
import Automaton.RE
