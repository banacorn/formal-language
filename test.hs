import Test.QuickCheck
import Control.Applicative
import Control.Monad
import Data.Set hiding (map)
import Data.List (nubBy, groupBy, nub)
import FA

--states = fromList [
--    singleton $ S "A", 
--    singleton $ S "B",
--    singleton $ S "C",
--    singleton $ S "D"
--    ]
--alphabets = fromList ['0', '1']

mappings = Map [
    (singleton $ S "1", 'b', singleton $ S "2"),
    (singleton $ S "1", 'a', singleton $ S "1"),
    (singleton $ S "2", 'b', singleton $ S "3"),
    (singleton $ S "2", 'a', singleton $ S "1"),
    (singleton $ S "3", 'b', singleton $ S "3"),
    (singleton $ S "3", 'a', singleton $ S "2")
    ]

--ndmappings = NDMap [
--    (singleton $ S "A", '0', fromList [singleton $ S "B"]),
--    (singleton $ S "A", ' ', fromList [singleton $ S "C"]),
--    (singleton $ S "B", '1', fromList [singleton $ S "B", singleton $ S "D"]),
--    (singleton $ S "C", ' ', fromList [singleton $ S "B"]),
--    (singleton $ S "C", '0', fromList [singleton $ S "D"]),
--    (singleton $ S "D", '0', fromList [singleton $ S "C"])
--    ]
--start = singleton $ S "A"
--accepts = fromList [singleton $ S "C", singleton $ S "D"]

states = fromList [
    singleton $ S "1", 
    singleton $ S "2",
    singleton $ S "3"
    ]
alphabets = fromList ['a', 'b']

ndmappings = NDMap [
    (singleton $ S "1", ' ', fromList [singleton $ S "3"]),
    (singleton $ S "1", 'b', fromList [singleton $ S "2"]),
    (singleton $ S "2", 'a', fromList [singleton $ S "2", singleton $ S "3"]),
    (singleton $ S "2", 'b', fromList [singleton $ S "3"]),
    (singleton $ S "3", 'a', fromList [singleton $ S "1"])
    ]

start = singleton $ S "1"
accepts = fromList [singleton $ S "1"]

nfa = NFA states alphabets ndmappings start accepts
dfa = DFA states alphabets mappings start accepts


ss = singleton . S

statesA = fromList [
    ss "1"
    ]
alphabetsA = fromList ['a']
ndmappingsA = NDMap [
    (ss "1", 'a', fromList [ss "1"])
    ]
startA = ss "1"
acceptsA = fromList [ss "1"]
nfaA = NFA statesA alphabetsA ndmappingsA startA acceptsA

genStates :: Gen (States Int)
genStates = fromList <$> fmap singleton <$> fmap S <$> listOf1 seed
    where seed = choose (0, 100) :: Gen Int

genAlphabets :: Gen Alphabets
genAlphabets =  fromList . nub <$> (listOf1 $ elements ['a' .. 'z'])

genLanguage :: Alphabets -> Gen Language
genLanguage = listOf . elements . toList


genCompleteMapping :: States a -> Alphabets -> Gen (Map a)
genCompleteMapping states alphabets = 
    let inits = [ (from, alphabet) | from <- toList states, alphabet <- toList alphabets] in
    fmap Map $ sequence $ fmap extend inits
    where   extend (from, alphabet) = do
                to <- elements $ toList states
                return (from, alphabet, to)

genPartialMapping :: (Eq a, Ord a) => States a -> Alphabets -> Gen (Map a)
genPartialMapping states alphabets = fmap NDMap $ listOf1 $ genNDArc states alphabets
    where   genNDArc states alphabets = do
                start <- elements $ toList states
                alphabet <- elements $ toList alphabets
                finals <- fmap (fromList . nub) . listOf1 . elements $ toList states
                return (start, alphabet, finals)

genDFA :: (Ord a, Show a) => States a -> Alphabets -> Gen (FA a)
genDFA states alphabets = do
    start <- elements $ toList states
    accepts <- listOf . elements $ toList states
    mappings <- genCompleteMapping states alphabets
    return $ DFA states alphabets mappings start (fromList accepts)

genNFA :: (Ord a) => States a -> Alphabets -> Gen (FA a)
genNFA states alphabets = do
    start <- elements $ toList states
    accepts <- listOf1 . elements $ toList states
    mappings <- genPartialMapping states alphabets
    return $ NFA states alphabets mappings start (fromList accepts)

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


propCompleteMapping :: Property
propCompleteMapping = do
    states <- genStates
    alphabets <- genAlphabets
    (Map mapping) <- genCompleteMapping states alphabets
    property $ length mapping == size states * size alphabets

propTransitionFunction :: Property
propTransitionFunction = do
    states <- genStates
    alphabets <- genAlphabets
    forAll (genCompleteMapping states alphabets) (\ maps ->
            let 
                (Map mappings) = maps
                transitions = driver maps
            in
            and $ map (\ (state, alphabet, target) -> transitions state alphabet == target ) mappings
        )



propDFA2NFA :: Property
propDFA2NFA = do
    states <- genStates
    alphabets <- genAlphabets
    mappings <- genCompleteMapping states alphabets
    start <- elements $ toList states
    accepts <- fmap fromList . listOf1 . elements $ toList states
    dfa <- return $ DFA states alphabets mappings start accepts
    nfa <- return $ dfa2nfa dfa
    forAll (genLanguage alphabets) (\language ->
            machine dfa language ==> machine nfa language
        )

propNFA2DFA :: Property
propNFA2DFA = do
    states <- genStates
    alphabets <- genAlphabets
    mappings <- genPartialMapping states alphabets
    start <- elements $ toList states
    accepts <- fmap fromList . listOf1 . elements $ toList states
    nfa <- return $ NFA states alphabets mappings start accepts
    dfa <- return $ nfa2dfa nfa
    forAll (genLanguage alphabets) (\language ->
            let prop = machine nfa language == machine dfa language in
            printTestCase (show dfa) prop
        )
motherfucker :: (Ord a) => FA a -> FA a
motherfucker = dfa2nfa . nfa2dfa
anotherfucker :: (Ord a) => FA a -> FA a
anotherfucker = motherfucker . motherfucker

