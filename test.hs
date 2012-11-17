import Test.QuickCheck
import Text.Printf

import Control.Applicative
import Control.Monad
import Automaton
import Data.List
import Debug.Trace




tests = [
    ("DFA Negation", quickCheck propNegateDFA),
    ("DFA Union", quickCheck propUnionDFA),
    ("DFA Intersection", quickCheck propIntersectDFA),
    ("DFA Concatenation", quickCheck propConcatenateDFA),
    ("DFA Kleene Star", quickCheck propKleeneStarDFA),
    ("NFA Negation", quickCheck propNegateNFA),
    ("NFA Union", quickCheck propUnionNFA),
    ("NFA Intersection", quickCheck propIntersectNFA),
    ("NFA Concatenation", quickCheck propConcatenateNFA),
    ("NFA Kleene Star", quickCheck propKleeneStarNFA),
    ("DFA => NFA", quickCheck propDFA2NFA),
    ("DFA <= NFA", quickCheck propNFA2DFA),
    ("DFA Minimization", quickCheck propMinimizeDFA)
    ]

main  = mapM_ (\(s,a) -> printf "%-25s: " s >> a) tests


bana test = replicateM_ 10 (quickCheck test)

--mains = replicateM_ 100 $ sample . join $ genMapping <$> genStates <*> genAlphabets
--main = q propNFA2DFA

------------------------------------------------------------------------
-- test data


-- dfa minimization test data
statesMin = [0..7]
alphabetsMin = [Alphabet '0', Alphabet '1']

mappingsMin = Map [
    (0, Alphabet '0', 1),
    (0, Alphabet '1', 5),
    (1, Alphabet '0', 6),
    (1, Alphabet '1', 2),
    (2, Alphabet '0', 0),
    (2, Alphabet '1', 2),
    (3, Alphabet '0', 2),
    (3, Alphabet '1', 6),
    (4, Alphabet '0', 7),
    (4, Alphabet '1', 5),
    (5, Alphabet '0', 2),
    (5, Alphabet '1', 6),
    (6, Alphabet '0', 6),
    (6, Alphabet '1', 4),
    (7, Alphabet '0', 6),
    (7, Alphabet '1', 2)
    ]

startMin = 0
acceptsMin = [2]
dfa = DFA statesMin alphabetsMin mappingsMin startMin acceptsMin

------------

statesM' = [0 .. 2]
alphabetsM' = [Alphabet '1', Alphabet '0']
mappingsM' = Map [
    (0, Alphabet '0', 1),
    (0, Alphabet '1', 2),
    (1, Alphabet '0', 2),
    (1, Alphabet '1', 0),
    (2, Alphabet '0', 0),
    (2, Alphabet '1', 2)
    ]
startM' = 0
acceptsM' = [1]
dfam' = DFA statesM' alphabetsM' mappingsM' startM' acceptsM'

------------

statesEq = [0 .. 2]
alphabetsEq = [Alphabet '1', Alphabet '0']
mappingsEq = Map [
    (0, Alphabet '0', 0),
    (0, Alphabet '1', 0)
    ]
startEq = 0
acceptsEq = [0]
dfae = DFA statesEq alphabetsEq mappingsEq startEq acceptsEq

---------

statesN = [0 .. 2]
alphabetsN = [Alphabet 'a', Alphabet 'b']
mappingsN = MapN [
    (0, Epsilon, [2]),
    (0, Alphabet 'b', [1]),
    (1, Alphabet 'a', [1, 2]),
    (1, Alphabet 'b', [2]),
    (2, Alphabet 'a', [0])
    ]
startN = 0
acceptsN = [0]

nfa = NFA statesN alphabetsN mappingsN startN acceptsN


statesM = [0 .. 1]
alphabetsM = [Alphabet 'a', Alphabet 'b']
mappingsM = MapN [
    (0, Epsilon, [1]),
    (0, Alphabet 'b', [1]),
    (1, Alphabet 'a', [0])
    ]
startM = 0
acceptsM = [1]

nfam = NFA statesM alphabetsM mappingsM startM acceptsM

---

statesF = [656, 101, 497]
alphabetsF = [Alphabet 'z']
mappingsF = Map [
    (656, Alphabet 'z', 101),
    (101, Alphabet 'z', 656),
    (497, Alphabet 'z', 101)
    ]
startF = 497
acceptsF = [656]
dfaf = DFA statesF alphabetsF mappingsF startF acceptsF

---

r = read "a b" :: RE
run = automatonN $ re2nfa r



------------------------------------------------------------------------
-- generators

genStates :: Gen States
genStates = fmap nub . listOf1 $ seed
    where seed = choose (0, 1000) :: Gen Int

genAlphabets :: Gen Alphabets
genAlphabets =  nub <$> (listOf1 . elements $ Alphabet <$> ['a' .. 'z'])

genLanguage :: Alphabets -> Gen Language
genLanguage = listOf . elements . map rip
    where   rip (Alphabet x) = x

genMapping :: States -> Alphabets -> Gen Map
genMapping states alphabets = 
    fmap Map $ sequence $ map extend pairs
    where   pair a b = (a, b)
            pairs = pair <$> states <*> alphabets
            extend (a, b) = do
                c <- elements states
                return (a, b, c)

genMappingN :: States -> Alphabets -> Gen Map
genMappingN states alphabets = 
    fmap MapN $ sequence $ map extend pairs
    where   pair a b = (a, b)
            pairs = pair <$> states <*> alphabets
            extend (a, b) = do
                c <- fmap nub . listOf1 . elements $ states
                return (a, b, c)


genDFA :: States -> Alphabets -> Gen DFA
genDFA states alphabets = do
    start <- elements states
    accepts <- fmap nub . listOf . elements $ states
    mappings <- genMapping states alphabets
    return $ DFA states alphabets mappings start accepts


genNFA :: States -> Alphabets -> Gen NFA
genNFA states alphabets = do
    start <- elements states
    accepts <- fmap nub . listOf . elements $ states
    mappings <- genMappingN states alphabets
    return $ NFA states alphabets mappings start accepts

------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
-- properties



alphabetTestLimit = fmap $ take 4
stateTestLimit = fmap $ take 20

propGenStates :: Property
propGenStates = do
    states <- genStates
    property $ states == nub states

propGenMapping :: Property
propGenMapping = do
    Map mapping <- join $ genMapping <$> genStates <*> genAlphabets
    property $ mapping == nub mapping 

propGenMappingN :: Property
propGenMappingN = do
    MapN mapping <- join $ genMappingN <$> genStates <*> genAlphabets
    property $ mapping == nub mapping



propNormalizeDFA :: Property
propNormalizeDFA = do
    states      <- genStates
    alphabets   <- genAlphabets
    dfa         <- genDFA states alphabets
    dfa'        <- return (normalizeDFA dfa)
    forAll (genLanguage alphabets) (\ language ->
            automaton dfa language == automaton dfa' language && formal dfa' 
        )
    where   formal (DFA states alphabets mappings start accepts) = 
                states == [0 .. (length states - 1)]

propTrimStatesDFA :: Property
propTrimStatesDFA = do
    states      <- genStates
    alphabets   <- genAlphabets
    dfa         <- genDFA states alphabets
    dfa'        <- return (trimUnreachableStates dfa)
    forAll (genLanguage alphabets) (\ language ->
            let prop = automaton dfa language == automaton dfa' language in
            printTestCase (show dfa ++ "\n" ++ show dfa') prop
        )



----------------------------
--
--  Minimize DFA
--
----------------------------

propMinimizeDFA :: Property
propMinimizeDFA = do
    states      <- stateTestLimit genStates
    alphabets   <- alphabetTestLimit genAlphabets
    dfa         <- genDFA states alphabets
    dfa'        <- return (minimizeDFA dfa)
    forAll (genLanguage alphabets) (\ language ->
            let prop = automaton dfa language == automaton dfa' language in
            printTestCase (show dfa ++ "\n" ++ show dfa') prop
        )

----------------------------
--
--  Negation
--
----------------------------



propNegateDFATwice :: Property
propNegateDFATwice = do
    states      <- genStates
    alphabets   <- genAlphabets
    dfa         <- genDFA states alphabets
    property (dfa == (negateDFA . negateDFA) dfa)

propNegateDFA :: Property
propNegateDFA = do
    alphabets   <- genAlphabets
    states      <- genStates
    dfa         <- genDFA states alphabets

    forAll (genLanguage alphabets) (\ language -> 
            automaton dfa language /= automaton (negateDFA dfa) language 
        )


propNegateNFA :: Property
propNegateNFA = do
    alphabets   <- alphabetTestLimit genAlphabets
    states      <- stateTestLimit genStates
    nfa         <- genNFA states alphabets

    forAll (genLanguage alphabets) (\ language ->
            let
                prop = automatonN nfa language /= automatonN (negateNFA nfa) language 
            in
            printTestCase (show nfa ++ "\n" ++ show (negateNFA nfa)) prop
        )

----------------------------
--
--  Union
--
----------------------------



propUnionDFA :: Property
propUnionDFA = do
    alphabets   <- alphabetTestLimit genAlphabets
    -- DFA 0
    states0     <- stateTestLimit genStates
    dfa0        <- genDFA states0 alphabets
    -- DFA 1
    states1     <- stateTestLimit genStates
    dfa1        <- genDFA states1 alphabets

    forAll (genLanguage alphabets) (\ language -> 
            let dfa = dfa0 `unionDFA` dfa1 in
            automaton dfa0 language == automaton dfa language ||
            automaton dfa1 language == automaton dfa language
        )


propUnionNFA :: Property
propUnionNFA = do
    alphabets   <- take 3 <$> genAlphabets
    -- NFA 0
    states0     <- take 4 <$> genStates
    nfa0        <- genNFA states0 alphabets
    -- NFA 1
    states1     <- take 4 <$> genStates
    nfa1        <- genNFA states1 alphabets

    forAll (genLanguage alphabets) (\ language -> 
            let nfa = nfa0 `unionNFA` nfa1 in
            automatonN nfa0 language == automatonN nfa language ||
            automatonN nfa1 language == automatonN nfa language
        )



----------------------------
--
--  Intersection
--
----------------------------



propIntersectDFA :: Property
propIntersectDFA = do
    alphabets   <- alphabetTestLimit genAlphabets
    -- DFA 0
    states0     <- stateTestLimit genStates
    dfa0        <- genDFA states0 alphabets
    -- DFA 1
    states1     <- stateTestLimit genStates
    dfa1        <- genDFA states1 alphabets

    forAll (genLanguage alphabets) (\ language -> 
            let dfa = dfa0 `intersectDFA` dfa1 in
            automaton dfa0 language ==> automaton dfa language &&
            automaton dfa1 language ==> automaton dfa language
        )

propIntersectNFA :: Property
propIntersectNFA = do
    alphabets   <- alphabetTestLimit genAlphabets
    -- NFA 0
    states0     <- take 4 <$> genStates
    nfa0        <- genNFA states0 alphabets
    -- NFA 1
    states1     <- take 4 <$> genStates
    nfa1        <- genNFA states1 alphabets

    forAll (genLanguage alphabets) (\ language -> 
            let 
                nfa = nfa0 `intersectNFA` nfa1 
                prop =  automatonN nfa0 language ==> automatonN nfa language &&
                        automatonN nfa1 language ==> automatonN nfa language
            in
            printTestCase (show nfa0 ++ "\n" ++ show nfa1  ++ "\n" ++ show nfa) prop
        )



----------------------------
--
--  Concatenation
--
----------------------------

propConcatenateDFA :: Property
propConcatenateDFA = do
    alphabets   <- alphabetTestLimit genAlphabets
    -- DFA 0
    states0     <- take 4 <$> genStates
    dfa0        <- genDFA states0 alphabets
    lang0       <- genLanguage alphabets
    -- DFA 1
    states1     <- take 4 <$> genStates
    dfa1        <- genDFA states1 alphabets
    lang1       <- genLanguage alphabets

    dfa         <- return $ dfa0 `concatenateDFA` dfa1

    printTestCase (show dfa0 ++ "\n" ++ show dfa1  ++ "\n" ++ show dfa) (automaton dfa0 lang0 && automaton dfa1 lang1 ==> automaton dfa (lang0 ++ lang1))


propConcatenateNFA :: Property
propConcatenateNFA = do
    alphabets   <- genAlphabets
    -- NFA 0
    states0     <- genStates
    nfa0        <- genNFA states0 alphabets
    lang0       <- genLanguage alphabets
    -- NFA 1
    states1     <- genStates
    nfa1        <- genNFA states1 alphabets
    lang1       <- genLanguage alphabets

    nfa         <- return $ nfa0 `concatenateNFA` nfa1 

    printTestCase (show nfa0 ++ "\n" ++ show nfa1  ++ "\n" ++ show nfa) (automatonN nfa0 lang0 && automatonN nfa1 lang1 ==> automatonN nfa (lang0 ++ lang1))



----------------------------
--
--  Kleene Star
--
----------------------------


propKleeneStarDFA :: Property
propKleeneStarDFA = do
    states      <- take 6 <$> genStates
    alphabets   <- alphabetTestLimit genAlphabets
    dfa         <- genDFA states alphabets
    forAll (take 5 <$> genLanguage alphabets) (\ language ->
            let
                dfaS                = kleeneStarDFA dfa
                repeatedLanguages   = take 5 $ iterate (++ language) ""
                results             = automaton dfaS <$> repeatedLanguages
                none                = head results
                once                = head $ tail results
                moreTimes           = tail $ tail results
                prop                = none && once ==> (and moreTimes == or moreTimes)
            in
            printTestCase (show dfa ++ "\n" ++ show dfaS  ++ "\n" ++ show repeatedLanguages ++ "\n" ++ show results) prop
        )



propKleeneStarNFA :: Property
propKleeneStarNFA = do
    states      <- stateTestLimit genStates
    alphabets   <- alphabetTestLimit genAlphabets
    nfa         <- genNFA states alphabets
    forAll (take 5 <$> genLanguage alphabets) (\ language ->
            let
                nfaS                = kleeneStarNFA nfa
                repeatedLanguages   = take 5 $ iterate (++ language) ""
                results             = automatonN nfaS <$> repeatedLanguages
                none                = head results
                once                = head $ tail results
                moreTimes           = tail $ tail results
                prop                = none && once ==> (and moreTimes == or moreTimes)
            in
            printTestCase (show nfa ++ "\n" ++ show nfaS  ++ "\n" ++ show repeatedLanguages ++ "\n" ++ show results) prop
        )


----------------------------
--
--  DFA <=> NFA
--
----------------------------


propDFA2NFA :: Property
propDFA2NFA = do
    states      <- genStates
    alphabets   <- genAlphabets
    dfa         <- genDFA states alphabets
    nfa         <- return (dfa2nfa dfa)
    forAll (genLanguage alphabets) (\language ->
            automaton dfa language == automatonN nfa language
        )


propNFA2DFA :: Property
propNFA2DFA = do
    states      <-  stateTestLimit genStates
    alphabets   <-  alphabetTestLimit genAlphabets
    nfa         <- genNFA states alphabets
    forAll (genLanguage alphabets) (\language ->
            let dfa = nfa2dfa nfa
                prop = automatonN nfa language == automaton dfa language || automatonN nfa language /= automaton dfa language  in
                printTestCase (show nfa) prop
        )


