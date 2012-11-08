module Automaton.RE where

data RE = A Char | N | E | Union RE RE | Concat RE RE | Star RE

instance Show RE where
    show (A a) = [a]
    show N = "∅"
    show E = ""
    show (Union a b) = "(" ++ show a ++ "|" ++ show b ++ ")"
    show (Concat a b) = show a ++ show b
    show (Star a) = show a ++ "*"

--instance Read RE where
--     readsPrec _ r = do
--    ("Z", s) <- lex r
--    return (Z, s)