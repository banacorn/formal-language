import Test.QuickCheck
import Control.Applicative
import Control.Monad
import Data.Set hiding (map)
import Data.List (nubBy, groupBy, nub)
import FA

states = fromList [S "A", S "B", S "C", S "D"]
alphabets = fromList ['0', '1']
transitions = ndtransition [
    (S "A", '0', fromList [S "B"]),
    (S "A", ' ', fromList [S "C"]),
    (S "B", '1', fromList [S "B", S "D"]),
    (S "C", ' ', fromList [S "B"]),
    (S "C", '0', fromList [S "D"]),
    (S "D", '0', fromList [S "C"])
    ]
start = S "A"
accepts = fromList [S "C", S "D"]


q1 = fromList [S "even", S "odd"]
aa = fromList ['0', '1']
t1 = transition [
    (S "even", '0', S "even"),
    (S "even", '1', S "odd"),
    (S "odd", '0', S "odd"),
    (S "odd", '1', S "even")
    ]
s1 = S "even"
f1 = fromList [S "odd"]



q2 = fromList [S "1", S "2"]
t2 = transition [
    (S "1", '0', S "1"),
    (S "1", '1', S "2"),
    (S "2", '0', S "2"),
    (S "2", '1', S "2")
    ]
s2 = S "1"
f2 = fromList [S "2"]

nfa = NFA states alphabets transitions start accepts
dfa1 = DFA q1 aa t1 s1 f1
dfa2 = DFA q2 aa t2 s2 f2


genStates :: Gen (State String)
genStates = fromList <$> fmap S <$> (listOf1 $ show <$> seed)
    where   seed = choose (0, 100) :: Gen Int

genAlphabets :: Gen Alphabets
genAlphabets =  fromList . nub <$> (listOf1 $ elements ['a' .. 'z'])

genCompleteGraph :: State a -> Alphabets -> Gen [Arc a]
genCompleteGraph states alphabets = 
    let inits = [ (from, alphabet) | from <- toList states, alphabet <- toList alphabets] in
    sequence $ fmap extend inits
    where   extend (from, alphabet) = do
                to <- elements $ toList states
                return (from, alphabet, to)



genDFA :: (Ord a) => State a -> Alphabets -> Gen (FA a)
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