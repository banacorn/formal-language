module Automaton (
    
    -----------------
    -- types
    -----------------

    State,
    States,
    Alphabet(..),
    SAlphabet,
    Alphabets,
    SAlphabets,
    Language,
    Transitions(..),

    -- Regular Language
    DFA(..),
    NFA(..),
    GNFA(..),
    RE(..),

    -- Context-free Language
    PDA(..),



    ---------------------------
    -- Regular Language
    ---------------------------

    driver,
    driverN,
    automaton,
    automatonN,

    dfa2nfa,
    nfa2dfa,

    trimUnreachableStates,
    undistinguishableStates,
    epsilonClosure,
    collectState,
    collectStates,
    collect,

    -- DFA


    negateDFA,
    unionDFA,
    intersectDFA,
    concatenateDFA,
    kleeneStarDFA,

    nubStatesDFA,
    minimizeDFA,
    normalizeDFA,    
    replaceStatesDFA,

    -- NFA
    
    negateNFA,
    unionNFA,
    intersectNFA,
    concatenateNFA,
    kleeneStarNFA,

    replaceStatesNFA,
    nubStatesNFA,
    normalizeNFA,

    -- RE
    re2nfa,
    nfa2gnfa,
    gnfa2re,
    alphabet2re,
    nfa2re,
    normalizeRE,


    ---------------------------
    -- Context-free Language
    ---------------------------

    driverPDA,
    automatonPDA





) where


--------------------------------------------------------------

import Automaton.Instances
import Automaton.Type
import Automaton.FA
import Automaton.RE
import Automaton.PDA
