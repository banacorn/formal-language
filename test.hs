import Test.QuickCheck
import Control.Applicative
import Control.Monad
import Data.Set hiding (map)
import Data.List (nubBy, groupBy, nub)
import FA

states = fromList [State "A", State "B", State "C", State "D"]
alphabets = fromList ['0', '1']
transitions = ndtransition [
    (State "A", '0', fromList [State "B"]),
    (State "A", ' ', fromList [State "C"]),
    (State "B", '1', fromList [State "B", State "D"]),
    (State "C", ' ', fromList [State "B"]),
    (State "C", '0', fromList [State "D"]),
    (State "D", '0', fromList [State "C"])
    ]
start = State "A"
accepts = fromList [State "C", State "D"]


q1 = fromList [State "even", State "odd"]
aa = fromList ['0', '1']
t1 = transition [
    (State "even", '0', State "even"),
    (State "even", '1', State "odd"),
    (State "odd", '0', State "odd"),
    (State "odd", '1', State "even")
    ]
s1 = State "even"
f1 = fromList [State "odd"]



q2 = fromList [State "1", State "2"]
t2 = transition [
    (State "1", '0', State "1"),
    (State "1", '1', State "2"),
    (State "2", '0', State "2"),
    (State "2", '1', State "2")
    ]
s2 = State "1"
f2 = fromList [State "2"]

nfa = NFA states alphabets transitions start accepts
dfa1 = DFA q1 aa t1 s1 f1
dfa2 = DFA q2 aa t2 s2 f2


genStates :: Gen (States String)
genStates = fromList <$> fmap State <$> (listOf1 $ show <$> seed)
    where   seed = choose (0, 100) :: Gen Int

genAlphabets :: Gen Alphabets
genAlphabets =  fromList . nub <$> (listOf1 $ elements ['a' .. 'z'])

genCompleteGraph :: States a -> Alphabets -> Gen [Arc a]
genCompleteGraph states alphabets = 
    let inits = [ (from, alphabet) | from <- toList states, alphabet <- toList alphabets] in
    sequence $ fmap extend inits
    where   extend (from, alphabet) = do
                to <- elements $ toList states
                return (from, alphabet, to)



genDFA :: (Ord a) => States a -> Alphabets -> Gen (FA a)
genDFA states alphabets = do
    start <- elements $ toList states
    accepts <- listOf . elements $ toList states
    transitions <- fmap transition $ (genCompleteGraph states alphabets)
    return $ DFA states alphabets transitions start (fromList accepts)

genLanguage :: Alphabets -> Gen Language
genLanguage = listOf . elements . toList

propNegateTwice :: Property
propNegateTwice =
    forAll (genDFA') (\dfa -> 
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