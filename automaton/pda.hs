module Automaton.PDA where

import Automaton.Type


driverPDA :: Transitions -> State -> Alphabet -> SAlphabet -> (State, SAlphabet)
driverPDA (TransitionsPDA transitions) state alphabet stacktop = head [ (t, push) | (s, a, pop, t, push) <- transitions, s == state, a == alphabet, pop == stacktop ]
