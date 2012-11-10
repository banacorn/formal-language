module Automaton.RE where

import Debug.Trace

infixr 5 :+
infixr 4 :|
data RE = A Char | N | E |  RE :| RE | RE :+ RE | Star RE





