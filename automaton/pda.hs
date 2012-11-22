module Automaton.PDA where

import Automaton.Type
import Automaton.Util

import Control.Applicative

automatonPDA :: PDA -> Language -> Bool
automatonPDA (PDA states alphabets stateAlphabets (TransitionsPDA transitions) state stackTop acceptStates) []
	| state `elem` acceptStates = True
	| or $ flip elem acceptStates <$> (epsilonClosure (TransitionsPDA transitions) state) = True
	| otherwise = False

