module Language.Util where

import Language.Type
import Data.List
import Control.Applicative
import Control.Monad



-- make mappings a function
driverDFA :: Transitions -> State -> Alphabet -> State
driverDFA (TransitionsDFA mappings) state alphabet =
    let result = [ f | (s, a, f) <- mappings, s == state, a == alphabet ] in
    case result of [] -> error $ show state ++ ", " ++ showAlphabet alphabet ++ " Transition not deinfed"
                   (x:xs) -> x
    where   showAlphabet Epsilon = "ɛ"
            showAlphabet (Alphabet a) = show a
-- make mappings a function
driverNFA :: Transitions -> State -> Alphabet -> States
driverNFA (TransitionsNFA mappings) state alphabet = 
    let result = [ f | (s, a, f) <- mappings, s == state, a == alphabet ] in
    case result of [] -> []
                   (x:xs) -> x

driverPDA :: Transitions -> State -> Alphabet -> StackElement -> [(State, StackElement)]
driverPDA (TransitionsPDA transitions) state alphabet stacktop = [ (t, push) | (s, a, pop, t, push) <- transitions, s == state, a == alphabet, pop == stacktop ]



epsilonClosure :: Transitions -> State -> States
epsilonClosure (TransitionsPDA transitions) state = nub . insert state . join $ epsilonClosure (TransitionsPDA transitions) . fst <$> driverPDA (TransitionsPDA transitions) state Epsilon Epsilon
epsilonClosure transitions state = nub . insert state . join $ epsilonClosure transitions <$> transitNFA state Epsilon
    where   transitNFA = driverNFA transitions
