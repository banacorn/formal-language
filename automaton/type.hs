module Automaton.Type (
    Language,
    State,
    States,
    Alphabet,
    Alphabets,
    DFA(..),
    NFA(..),

    Transition,
    NDTransition,

    Map(..),
    Mapping,
    NDMapping
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
type NDMapping = (State, Alphabet, States)


data Map = Map [Mapping]
         | NDMap [NDMapping]

data DFA = DFA States Alphabets Map State States
data NFA = NFA States Alphabets Map State States
