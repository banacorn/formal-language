import Test.QuickCheck
import Control.Applicative
import Control.Monad
import Automaton
import Data.List


--main  = mapM_ (\(s,a) -> printf "%-25s: " s >> a) tests


tests = [
    ("~~dfa == dfa", quickCheck propNegateDFATwice),
    ("~dfa /= dfa", quickCheck propComplementary),
    ("dfa union", quickCheck propUnionDFA),
    ("dfa intersection", quickCheck propIntersectionDFA)
    ]

bana test = replicateM_ 10 (quickCheck test)

main = quickCheck propNFA2DFA

------------------------------------------------------------------------
-- test data


-- dfa minimization test data
statesMin = [0..7]
alphabetsMin = ['0', '1']

mappingsMin = Map [
    (0, '0', 1),
    (0, '1', 5),
    (1, '0', 6),
    (1, '1', 2),
    (2, '0', 0),
    (2, '1', 2),
    (3, '0', 2),
    (3, '1', 6),
    (4, '0', 7),
    (4, '1', 5),
    (5, '0', 2),
    (5, '1', 6),
    (6, '0', 6),
    (6, '1', 4),
    (7, '0', 6),
    (7, '1', 2)
    ]

startMin = 0
acceptsMin = [2]
dfaMin = DFA statesMin alphabetsMin mappingsMin startMin acceptsMin


------------

statesEq = [0 .. 1]
alphabetsEq = ['1', '0']
mappingsEq = Map [
    (0, '0', 0),
    (0, '1', 0)
    ]
startEq = 0
acceptsEq = [0]
e = DFA statesEq alphabetsEq mappingsEq startEq acceptsEq

---------

statesN = [0 .. 2]
alphabetsN = ['a', 'b']
mappingsN = MapN [
    (0, ' ', [2]),
    (0, 'b', [1]),
    (1, 'a', [1, 2]),
    (1, 'b', [2]),
    (2, 'a', [0])
    ]
startN = 0
acceptsN = [0]

nfa = NFA statesN alphabetsN mappingsN startN acceptsN


statesM = [0 .. 1]
alphabetsM = ['a', 'b']
mappingsM = MapN [
    (0, ' ', [1]),
    (0, 'b', [1]),
    (1, 'a', [0])
    ]
startM = 0
acceptsM = [1]

nfam = NFA statesM alphabetsM mappingsM startM acceptsM

u = unionNFA nfa nfam

------------------------------------------------------------------------
-- generators

genStates :: Gen States
genStates = fmap nub . listOf1 $ seed
    where seed = choose (0, 100) :: Gen Int

genAlphabets :: Gen Alphabets
genAlphabets =  nub <$> (listOf1 $ elements ['a' .. 'z'])

genLanguage :: Alphabets -> Gen Language
genLanguage = listOf . elements


genCompleteMapping :: States -> Alphabets -> Gen Map
genCompleteMapping states alphabets = 
    fmap Map $ sequence $ map extend pairs
    where   pair a b = (a, b)
            pairs = (pair <$> states <*> alphabets)
            extend (a, b) = do
                c <- elements states
                return (a, b, c)

genPartialMapping :: States -> Alphabets -> Gen Map
genPartialMapping states alphabets = 
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
    mappings <- genCompleteMapping states alphabets
    return $ DFA states alphabets mappings start accepts


genNFA :: States -> Alphabets -> Gen NFA
genNFA states alphabets = do
    start <- elements states
    accepts <- fmap nub . listOf . elements $ states
    mappings <- genPartialMapping states alphabets
    return $ NFA states alphabets mappings start accepts

------------------------------------------------------------------------
-- properties



propNegateDFATwice :: Property
propNegateDFATwice = do
    states <- genStates
    alphabets <- genAlphabets
    dfa <- genDFA states alphabets
    forAll (genLanguage alphabets) (\ language -> 
            automaton dfa language == automaton (negateDFA . negateDFA $ dfa) language
        )
    --property (dfa == (negateDFA . negateDFA) dfa)


propComplementary :: Property
propComplementary = do
    alphabets <- genAlphabets
    states <- genStates
    dfa <- genDFA states alphabets

    forAll (genLanguage alphabets) (\ language -> 
            automaton dfa language /= automaton (negateDFA dfa) language 
        )


propUnionDFA :: Property
propUnionDFA = do
    alphabets <- genAlphabets
    -- DFA 0
    states0 <- genStates
    dfa0 <- genDFA states0 alphabets
    -- DFA 1
    states1 <- genStates
    dfa1 <- genDFA states1 alphabets

    forAll (genLanguage alphabets) (\ language -> 
            let dfa = dfa0 `unionDFA` dfa1 in
            automaton dfa0 language == automaton dfa language ||
            automaton dfa1 language == automaton dfa language
        )



propIntersectionDFA :: Property
propIntersectionDFA = do
    alphabets <- genAlphabets
    -- DFA 0
    states0 <- genStates
    dfa0 <- genDFA states0 alphabets
    -- DFA 1
    states1 <- genStates
    dfa1 <- genDFA states1 alphabets

    forAll (genLanguage alphabets) (\ language -> 
            let dfa = dfa0 `intersectionDFA` dfa1 in
            automaton dfa0 language ==> automaton dfa language &&
            automaton dfa1 language ==> automaton dfa language
        )

propFormalizeDFA :: Property
propFormalizeDFA = do
    states      <- genStates
    alphabets   <- genAlphabets
    dfa         <- genDFA states alphabets
    dfa'        <- return (formalizeDFA dfa)
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


propMinimizeDFA :: Property
propMinimizeDFA = do
    states      <- genStates
    alphabets   <- genAlphabets
    dfa         <- genDFA states alphabets
    dfa'        <- return (minimizeDFA dfa)
    forAll (genLanguage alphabets) (\ language ->
            let prop = automaton dfa language == automaton dfa' language in
            let dfa'' = trimUnreachableStates dfa in
            printTestCase (show dfa ++ "\n" ++ show dfa'' ++ "\n" ++ show dfa') prop
        )

propDFA2NFA :: Property
propDFA2NFA = do
    states <- genStates
    alphabets <- genAlphabets
    dfa <- genDFA states alphabets
    nfa <- return (dfa2nfa dfa)
    forAll (genLanguage alphabets) (\language ->
            automaton dfa language == automatonN nfa language
        )
--propTransitionFunction :: Property
--propTransitionFunction = do
--    states <- genStates
--    alphabets <- genAlphabets
--    forAll (genCompleteMapping states alphabets) (\ maps ->
--            let 
--                (Map mappings) = maps
--                transitions = driver maps
--            in
--            and $ map (\ (state, alphabet, target) -> transitions state alphabet == target ) mappings
--        )



propNFA2DFA :: Property
propNFA2DFA = do
    states <- genStates
    alphabets <- genAlphabets
    nfa <- genNFA states alphabets
    dfa <- return $ nfa2dfa nfa
    forAll (genLanguage alphabets) (\language ->
            let prop = automatonN nfa language == automaton dfa language in
            printTestCase (show dfa) prop
        )

