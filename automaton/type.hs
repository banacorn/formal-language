module Automaton.Type where


class Automaton a where
    automaton :: a -> Language -> Bool
class Automaton a => FiniteAutomaton a where
    negate :: a -> a
    union :: a -> a -> a
    intersect :: a -> a -> a
    concatenate :: a -> a -> a
    kleeneStar :: a -> a

    --normalize :: a -> a
    --minimize :: a -> a
--------------------------------------------------------------
-- Data Types
--------------------------------------------------------------

type State  = Int
type States = [State]

data Alphabet = Alphabet Char | Epsilon deriving (Eq, Ord)
type StackElement = Alphabet
type Language = String
type Alphabets = [Alphabet]
type StackElements = [StackElement]

type TransitionDFA = (State, Alphabet, State)
type TransitionNFA = (State, Alphabet, States)
type TransitionRE = (State, RE, State)
type TransitionPDA = (State, Alphabet, StackElement, State, StackElement)


data Transitions = TransitionsDFA [TransitionDFA]
                 | TransitionsNFA [TransitionNFA]
                 | TransitionsRE [TransitionRE]
                 | TransitionsPDA [TransitionPDA]

data DFA = DFA States Alphabets Transitions State States
data NFA = NFA States Alphabets Transitions State States
data GNFA = GNFA States Alphabets Transitions State States


--- RE

infixr 5 :+
infixr 4 :|
data RE = A Char | N | E |  RE :| RE | RE :+ RE | Star RE deriving Eq




------------------------------------------
-- Context-free Language
------------------------------------------


-- PDA

data PDA = PDA States Alphabets StackElements Transitions State StackElement States

-- CFG
data Symbol = V Int | T Char
type Symbols = [Symbol]
type Rule = (Symbol, Symbols)
type Rules = [Rule]
data CFG = CFG Symbols Symbols Symbol Rules




