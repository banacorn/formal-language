module Automaton.PDA where

import Automaton.Type


driverPDA :: Transitions -> State -> Alphabet -> SAlphabet -> (State, SAlphabet)
driverPDA (TransitionsPDA transitions) state alphabet stacktop = head [ (t, push) | (s, a, pop, t, push) <- transitions, s == state, a == alphabet, pop == stacktop ]

automatonPDA :: PDA -> Language -> Bool
automatonPDA (PDA states alphabets stateAlphabets (TransitionsPDA transitions) state stackTop acceptStates) []
	| state `elem` acceptStates = True
	| otherwise = False

