module Automaton.Type (
    Language,
    State,
    States,
    Alphabet,
    Alphabets,
    DFA(..),
    NFA(..),

    RE(..),

    Transition,
    NDTransition,

    Map(..),
    Mapping,
    MappingN
) where


--------------------------------------------------------------

--import qualified Data.IntMap as IntMap


--------------------------------------------------------------

type State  = Int
type States = [State]

type Alphabet = Char
type Language = [Alphabet]
type Alphabets = [Alphabet]

type Transition = State -> Alphabet -> State
type NDTransition = State -> Alphabet -> States

type Mapping = (State, Alphabet, State)
type MappingN = (State, Alphabet, States)


data Map = Map [Mapping]
         | MapN [MappingN]

data DFA = DFA States Alphabets Map State States
data NFA = NFA States Alphabets Map State States


--- RE

infixr 5 :+
infixr 4 :|
data RE = A Char | N | E |  RE :| RE | RE :+ RE | Star RE deriving Eq

