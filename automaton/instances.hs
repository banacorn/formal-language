module Automaton.Instances (Show(..), Eq(..)) where

import Automaton.Type
import Automaton.FA

import Data.List


--------------------------------------------------------------


dropQuote :: String -> String
dropQuote [] = []
dropQuote ('"':xs) = dropQuote xs
dropQuote ('\\':xs) = dropQuote xs
dropQuote ('\'':xs) = dropQuote xs
dropQuote ('8':'7':'0':'9':xs) = '∅' : dropQuote xs
dropQuote (x:xs) = x : dropQuote xs



instance Show Map where
    show (Map mappings) = dropQuote $ 
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
    show (NDMap mappings) = dropQuote $
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



instance Eq DFA where
    (==) dfa0 dfa1 = alphabetDFA0 == alphabetDFA1 && null accepts
        where   (DFA _ _ _ _ accepts) = trimUnreachableStates wtf
                wtf   = (dfa0 `intersectionDFA` _dfa1) `unionDFA` (_dfa0 `intersectionDFA` dfa1)
                _dfa0 = negateDFA dfa0
                _dfa1 = negateDFA dfa1
                alphabet (DFA _ a _ _ _) = a
                alphabetDFA0 = sort $ alphabet dfa0
                alphabetDFA1 = sort $ alphabet dfa1