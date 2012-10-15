module Automaton.Type (
    Language,
    State,
    States,
    Alphabet,
    Alphabets,
    FA(..),

    Transition,
    NDTransition,

    Map(..),
    Mapping,
    NDMapping
) where


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

data FA = DFA States Alphabets Map State States
        | NFA States Alphabets Map State States
