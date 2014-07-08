module Language.PDA where

import Language.Type
import Language.Util

import Control.Applicative
import Debug.Trace


automatonPDA :: PDA -> Language -> Bool

-- rejects everything if there are no accept states
automatonPDA (PDA _ _ _ _ _ _ []) _ = False

automatonPDA (PDA states alphabets stateAlphabets transitions state stackTop acceptStates) []
    -- if the closure of the current state has one of the accept states
    | or $ flip elem acceptStates <$> closure = True
    | otherwise = False
    where   closure = epsilonClosure transitions state

automatonPDA (PDA states alphabets stateAlphabets transitions state stackTop acceptStates) (x:xs)
    | (Alphabet x) `notElem` alphabets = False
    | otherwise = or $ consume (x:xs) (state, stackTop)
    where   closure state = traceShow state $ zip (epsilonClosure transitions state) (repeat stackTop)
            jump x (state, stacktop) = driverPDA transitions state x stacktop
            accept (state, stacktop) = return (state `elem` acceptStates)
            consume [] (state, stacktop) = closure state >>= accept
            consume (x:xs) (state, stacktop) = closure state >>= jump (Alphabet x) >>= consume xs