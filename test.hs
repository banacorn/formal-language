import Test.QuickCheck
import Control.Applicative
import Control.Monad
import Automaton
import Data.List

genStates :: Gen States
genStates = listOf1 seed
    where seed = choose (0, 100) :: Gen Int

genAlphabets :: Gen Alphabets
genAlphabets =  nub <$> (listOf1 $ elements ['a' .. 'z'])

genLanguage :: Alphabets -> Gen Language
genLanguage = listOf . elements


genCompleteMapping :: States -> Alphabets -> Gen Map
genCompleteMapping states alphabets = 
    fmap Map $ sequence $ map extend pairs
    where   pair a b = (a, b)
            pairs = pair <$> states <*> alphabets
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
    accepts <- listOf . elements $ states
    mappings <- genCompleteMapping states alphabets
    return $ DFA states alphabets mappings start accepts


--propNegateTwice :: Property
--propNegateTwice =
--    forAll genDFA' (\dfa -> 
--        let __dfa = negateFA . negateFA $ dfa in
--        forAll (genAlphabets >>= genLanguage) (\language ->
--            machine dfa language == machine __dfa language
--        )
--    )
--    where genDFA' = join $ genDFA <$> genStates <*> genAlphabets

--propComplementary :: Property
--propComplementary = do
--    alphabets <- genAlphabets
--    states <- genStates
--    forAll (genDFA states alphabets) (\dfa ->
--            let _dfa = negateFA dfa in 
--            forAll (genLanguage alphabets) (\language ->
--                machine dfa language /= machine _dfa language
--            )
--        )


--propCompleteMapping :: Property
--propCompleteMapping = do
--    states <- genStates
--    alphabets <- genAlphabets
--    (Map mapping) <- genCompleteMapping states alphabets
--    property $ length mapping == size states * size alphabets

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

