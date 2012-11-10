module Automaton.RE where

import Debug.Trace
import Text.ParserCombinators.Parsec

infixr 5 :+
infixr 4 :|
data RE = A Char | N | E |  RE :| RE | RE :+ RE | Star RE


instance Show RE where
    show (A a) = [a]
    show N = "∅"
    show E = " "
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
        char ' '
        do
            char '*'
            return (Star (E))
            <|> return (E)
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
        return $ foldr1 (:+) a

reParser :: Parser RE
reParser =
    do
        a <- concatParser
        do
            char '|'
            b <- concatParser
            return (a :| b)
            <|> return a





