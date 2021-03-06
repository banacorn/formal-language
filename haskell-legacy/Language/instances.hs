module Language.Instances (Show(..), Eq(..)) where

import Language.Type
import Language.FA
import Language.RE
import Text.ParserCombinators.Parsec

import Prelude hiding (negate)
import qualified Data.List as List
import Debug.Trace


--------------------------------------------------------------


dropQuote :: String -> String
dropQuote [] = []
dropQuote ('"':xs) = dropQuote xs
dropQuote ('\\':xs) = dropQuote xs
dropQuote ('\'':xs) = dropQuote xs
dropQuote ('8':'7':'0':'9':xs) = '∅' : dropQuote xs
dropQuote (x:xs) = x : dropQuote xs


instance Show Alphabet where
    show (Alphabet a) = show a
    show Epsilon = "ɛ"


instance Show Transitions where
    show (TransitionsPDA mappings) = dropQuote $ 
        listMapping mappings
        where
            listMapping = concat . fmap (prefixIndent . showMap)
            prefixIndent = (++) "\n        "
            showMap (s, a, p, t, q) = 
                show s ++ 
                "  ×  " ++ 
                show a ++ 
                "  ×  " ++ 
                show p ++ 
                "  →  " ++ 
                show t ++
                "  ×  " ++ 
                show q 

    show (TransitionsDFA mappings) = dropQuote $ 
        listMapping mappings
        where
            listMapping = concat . fmap (prefixIndent . showMap)
            prefixIndent = (++) "\n        "
            showMap (s, a, t) = 
                show s ++ 
                "  ×  " ++ 
                show a ++ 
                "  →  " ++ 
                show t
    show (TransitionsNFA mappings) = dropQuote $
        listMapping mappings
        where
            listMapping = concat . fmap (prefixIndent . showMap)
            prefixIndent = (++) "\n        "
            showMap (s, a, t) = 
                show s ++ 
                "  ×  " ++ 
                show a ++ 
                "  →  " ++ 
                show t   
    show (TransitionsRE mappings) = dropQuote $
        listMapping mappings
        where
            listMapping = concat . fmap (prefixIndent . showMap)
            prefixIndent = (++) "\n        "
            showMap (s, a, t) = 
                show s ++ 
                "  ×  " ++ 
                show a ++ 
                "  →  " ++ 
                show t


instance Show DFA where
    show (DFA states alphabets mappings state accepts) = dropQuote $
        "DFA" ++
        "\n    Q   " ++ (show states) ++ 
        "\n    Σ   " ++ (show alphabets) ++
        "\n    δ   " ++ (show mappings) ++
        "\n    q   " ++ (show state) ++ 
        "\n    F   " ++ (show accepts) ++
        "\n"
instance Show NFA where
    show (NFA states alphabets mappings state accepts) = dropQuote $ 
        "NFA" ++
        "\n    Q   " ++ (show states) ++ 
        "\n    Σ   " ++ (show alphabets) ++
        "\n    δ   " ++ (show mappings) ++
        "\n    q   " ++ (show state) ++ 
        "\n    F   " ++ (show accepts) ++
        "\n"
instance Show GNFA where
    show (GNFA states alphabets mappings state accepts) = dropQuote $ 
        "GNFA" ++
        "\n    Q   " ++ (show states) ++ 
        "\n    Σ   " ++ (show alphabets) ++
        "\n    δ   " ++ (show mappings) ++
        "\n    q   " ++ (show state) ++ 
        "\n    F   " ++ (show accepts) ++
        "\n"






instance Eq DFA where
    (==) dfa0 dfa1 = alphabetDFA0 == alphabetDFA1 && null accepts
        where   (DFA _ _ _ _ accepts) = trimUnreachableStates wtf
                wtf   = (dfa0 `intersect` _dfa1) `union` (_dfa0 `intersect` dfa1)
                _dfa0 = negate dfa0
                _dfa1 = negate dfa1
                alphabet (DFA _ a _ _ _) = a
                alphabetDFA0 = List.sort $ alphabet dfa0
                alphabetDFA1 = List.sort $ alphabet dfa1


instance Eq NFA where
    (==) nfa0 nfa1 = nfa2dfa nfa0 == nfa2dfa nfa1




--------------------------------------------------------------




    

instance Show RE where
    show (A a) = [a]
    show N = "∅"
    show E = "ɛ"
    show (a :| b) = "(" ++ show a ++ "|" ++ show b ++ ")"
    show (a :+ b) = show a ++ show b
    show (Star a) = show a ++ "*"

instance Read RE where
    readsPrec _ input = case parse reParser "Regular Expression" input of
        Right x -> [(x, "")]

unitParser :: Parser RE
unitParser =
    do
        char '('
        inside <- reParser
        char ')'
        do
            char '*'
            return (Star inside)
            <|> return (inside)
    <|> 
    do
        char '∅'
        do
            char '*'
            return (E)
            <|> return (N)
    <|> 
    do
        char 'ɛ'
        do
            char '*'
            return (Star (E))
            <|> return (E)
    <|> 
    do
        char ' '
        do
            char '*'
            return (Star (A ' '))
            <|> return (A ' ')
    <|> 
    do
        c <- digit
        do
            char '*'
            return (Star (A c))
            <|> return (A c)
    <|> 
    do
        c <- letter
        do
            char '*'
            return (Star (A c))
            <|> return (A c)

concatParser :: Parser RE
concatParser = 
    do 
        a <- many1 unitParser
        return $ if (N `elem` a) then N else (foldr1 (:+) a)

reParser :: Parser RE
reParser =
    do
        a <- concatParser
        do
            char '|'
            b <- concatParser
            return (a :| b)
            <|> return a
