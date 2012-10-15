import Test.QuickCheck
import Control.Applicative
import Control.Monad
import Automaton
import Data.List
import Text.Printf


main  = mapM_ (\(s,a) -> printf "%-25s: " s >> a) tests


tests = [
    ("~~dfa == dfa", quickCheck propNegateDFATwice),
    ("~dfa /= dfa", quickCheck propComplementary),
    ("union dfa", quickCheck propUnionDFA)
    ]



------------------------------------------------------------------------
-- test data

q0 = [1..5]
a = ['a' .. 'd']




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
            pairs = nub $ (pair <$> states <*> alphabets)
            extend (a, b) = do
                c <- elements states
                return (a, b, c)

genPartialMapping :: States -> Alphabets -> Gen Map
genPartialMapping states alphabets = 
    fmap NDMap $ sequence $ map extend pairs
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



--propDFA2NFA :: Property
--propDFA2NFA = do
--    states <- genStates
--    alphabets <- genAlphabets
--    dfa <- genDFA states alphabets
--    nfa <- return $ dfa2nfa dfa
--    forAll (genLanguage alphabets) (\language ->
--            machine dfa language ==> machine nfa language
--        )

--propNFA2DFA :: Property
--propNFA2DFA = do
--    states <- genStates
--    alphabets <- genAlphabets
--    nfa <- genNFA states alphabets
--    dfa <- return $ nfa2dfa nfa
--    forAll (genLanguage alphabets) (\language ->
--            let prop = machine nfa language == machine dfa language in
--            printTestCase (show dfa) prop
--        )

