module Automaton.Type where

-- (
--    Language,
--    State,
--    States,
--    Alphabet(..),
--    Alphabets,
--    DFA(..),
--    NFA(..),
--    GNFA(..),

--    RE(..),

--    Transition,
--    NDTransition,

--    Map(..),
--    Mapping,
--    MappingN
--) where


--------------------------------------------------------------

--import qualified Data.IntMap as IntMap


--------------------------------------------------------------

type State  = Int
type States = [State]

data Alphabet = Alphabet Char | Epsilon deriving (Eq, Ord)
type Language = String
type Alphabets = [Alphabet]

type Transition = State -> Alphabet -> State
type NDTransition = State -> Alphabet -> States

type Mapping = (State, Alphabet, State)
type MappingN = (State, Alphabet, States)
type MappingRE = (State, RE, State)


data Map = Map [Mapping]
         | MapN [MappingN]
         | MapRE [MappingRE]

data DFA = DFA States Alphabets Map State States
data NFA = NFA States Alphabets Map State States
data GNFA = GNFA States Alphabets Map State States


--- RE

infixr 5 :+
infixr 4 :|
data RE = A Char | N | E |  RE :| RE | RE :+ RE | Star RE deriving Eq




------------------------------------------
-- Context-free Language
------------------------------------------

data Symbol = V Int | T Char
type Symbols = [Symbol]
type Rule = (Symbol, Symbols)
type Rules = [Rule]
data CFG = CFG Symbols Symbols Symbol Rules




