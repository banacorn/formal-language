module Automaton.Type where



--------------------------------------------------------------

--import qualified Data.IntMap as IntMap


--------------------------------------------------------------

type State  = Int
type States = [State]

data Alphabet = Alphabet Char | Epsilon deriving (Eq, Ord)
type SAlphabet = Alphabet
type Language = String
type Alphabets = [Alphabet]
type SAlphabets = [SAlphabet]

type TransitionDFA = (State, Alphabet, State)
type TransitionNFA = (State, Alphabet, States)
type TransitionRE = (State, RE, State)
type TransitionPDA = (State, Alphabet, SAlphabet, State, SAlphabet)


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

data PDA = PDA States Alphabets SAlphabets Transitions State SAlphabet States

-- CFG
data Symbol = V Int | T Char
type Symbols = [Symbol]
type Rule = (Symbol, Symbols)
type Rules = [Rule]
data CFG = CFG Symbols Symbols Symbol Rules




