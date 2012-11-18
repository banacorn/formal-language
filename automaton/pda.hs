module Automaton.PDA where

driverPDA :: Transitions -> State -> Alphabet -> SAlphabet -> (State, SAlphabet)
driverPDA (TransitionsPDA transitions) state alphabet stacktop = [ (t, push) | (s, a, pop, t, push) <- transitions, s == state, a == alphabet, pop == stacktop ]
