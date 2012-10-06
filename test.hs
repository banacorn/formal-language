import Test.QuickCheck
import Control.Applicative
import Control.Monad
import Data.Set hiding (map)
import Data.List (nubBy, groupBy, nub)
import FA

states = fromList [
    singleton $ S "A", 
    singleton $ S "B",
    singleton $ S "C",
    singleton $ S "D"
    ]
alphabets = fromList ['0', '1']

transitions = transition [
    (singleton $ S "A", '1', singleton $ S "B"),
    (singleton $ S "A", '0', singleton $ S "A"),
    (singleton $ S "B", '1', singleton $ S "C"),
    (singleton $ S "B", '0', singleton $ S "A"),
    (singleton $ S "C", '1', singleton $ S "D"),
    (singleton $ S "C", '0', singleton $ S "B"),
    (singleton $ S "D", '1', singleton $ S "D"),
    (singleton $ S "D", '0', singleton $ S "C")
    ]

ndtransitions = ndtransition [
    (singleton $ S "A", '0', fromList [singleton $ S "B"]),
    (singleton $ S "A", ' ', fromList [singleton $ S "C"]),
    (singleton $ S "B", '1', fromList [singleton $ S "B", singleton $ S "D"]),
    (singleton $ S "C", ' ', fromList [singleton $ S "B"]),
    (singleton $ S "C", '0', fromList [singleton $ S "D"]),
    (singleton $ S "D", '0', fromList [singleton $ S "C"])
    ]
start = singleton $ S "A"
accepts = fromList [singleton $ S "C", singleton $ S "D"]

nfa = NFA states alphabets ndtransitions start accepts
dfa = DFA states alphabets transitions start accepts


genStates :: Gen (States Int)
genStates = fromList <$> fmap singleton <$> fmap S <$> listOf1 seed
    where seed = choose (0, 100) :: Gen Int

genAlphabets :: Gen Alphabets
genAlphabets =  fromList . nub <$> (listOf1 $ elements ['a' .. 'z'])

genLanguage :: Alphabets -> Gen Language
genLanguage = listOf . elements . toList


genCompleteMapping :: States a -> Alphabets -> Gen [(State a, Alphabet, State a)]
genCompleteMapping states alphabets = 
    let inits = [ (from, alphabet) | from <- toList states, alphabet <- toList alphabets] in
    sequence $ fmap extend inits
    where   extend (from, alphabet) = do
                to <- elements $ toList states
                return (from, alphabet, to)

genPartialMapping :: (Eq a, Ord a) => States a -> Alphabets -> Gen [(State a, Alphabet, States a)]
genPartialMapping states alphabets = listOf1 $ genNDArc states alphabets
    where   genNDArc states alphabets = do
                start <- elements $ toList states
                alphabet <- elements $ toList alphabets
                finals <- fmap (fromList . nub) . listOf1 . elements $ toList states
                return (start, alphabet, finals)

genTransitionFunction :: (Eq a, Show a) => States a -> Alphabets -> Gen (State a -> Alphabet -> State a)
genTransitionFunction states alphabets = (genCompleteMapping states alphabets) >>= return . transition

genNDTransitionFunction :: (Eq a, Ord a) => States a -> Alphabets -> Gen (State a -> Alphabet -> States a)
genNDTransitionFunction states alphabets = (genPartialMapping states alphabets) >>= return . ndtransition

genDFA :: (Ord a, Show a) => States a -> Alphabets -> Gen (FA a)
genDFA states alphabets = do
    start <- elements $ toList states
    accepts <- listOf . elements $ toList states
    transitions <- fmap transition $ (genCompleteMapping states alphabets)
    return $ DFA states alphabets transitions start (fromList accepts)

genNFA :: (Ord a) => States a -> Alphabets -> Gen (FA a)
genNFA states alphabets = do
    start <- elements $ toList states
    accepts <- listOf1 . elements $ toList states
    transitions <- fmap ndtransition $ (genPartialMapping states alphabets)
    return $ NFA states alphabets transitions start (fromList accepts)

propNegateTwice :: Property
propNegateTwice =
    forAll genDFA' (\dfa -> 
        let __dfa = negateFA . negateFA $ dfa in
        forAll (genAlphabets >>= genLanguage) (\language ->
            machine dfa language == machine __dfa language
        )
    )
    where genDFA' = join $ genDFA <$> genStates <*> genAlphabets

propComplementary :: Property
propComplementary = do
    alphabets <- genAlphabets
    states <- genStates
    forAll (genDFA states alphabets) (\dfa ->
            let _dfa = negateFA dfa in 
            forAll (genLanguage alphabets) (\language ->
                machine dfa language /= machine _dfa language
            )
        )



propTransition2NDTransition :: Property
propTransition2NDTransition = do
    states <- genStates
    alphabets <- genAlphabets
    mappings <- genCompleteMapping states alphabets
    forAll (return mappings) (\mappings ->
            let 
                transitions = transition mappings
                ndtransitions = transition2ndtransition transitions 
                mapping = [ transitions state alphabet | state <- toList states, alphabet <- toList alphabets]
                ndmapping = [ ndtransitions state alphabet | state <- toList states, alphabet <- toList alphabets]
            in
            fmap singleton mapping == ndmapping
        )

propCompleteMapping :: Property
propCompleteMapping = do
    states <- genStates
    alphabets <- genAlphabets
    mapping <- genCompleteMapping states alphabets
    property $ length mapping == size states * size alphabets

propTransitionFunction :: Property
propTransitionFunction = do
    states <- genStates
    alphabets <- genAlphabets
    forAll (genCompleteMapping states alphabets) (\ mappings ->
            let transitions = transition mappings in
            and $ map (\ (state, alphabet, target) -> transitions state alphabet == target ) mappings
        )



propDFA2NFA :: Property
propDFA2NFA = do
    states <- genStates
    alphabets <- genAlphabets
    transitions <- genTransitionFunction states alphabets
    start <- elements $ toList states
    accepts <- fmap fromList . listOf1 . elements $ toList states
    dfa <- return $ DFA states alphabets transitions start accepts
    nfa <- return $ dfa2nfa dfa
    forAll (genLanguage alphabets) (\language ->
            machine dfa language ==> machine nfa language
        )


