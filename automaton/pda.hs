module Automaton.PDA where

import Automaton.Type
import Automaton.Util

import Control.Applicative


automatonPDA :: PDA -> Language -> Bool

-- rejects everything if there are no accept states
automatonPDA (PDA _ _ _ _ _ _ []) _ = False
automatonPDA (PDA states alphabets stateAlphabets (TransitionsPDA transitions) state stackTop acceptStates) []
    | state `elem` acceptStates = True
    | or $ flip elem acceptStates <$> (epsilonClosure (TransitionsPDA transitions) state) = True
    | otherwise = False

