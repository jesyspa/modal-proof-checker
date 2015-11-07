module Main where

import Checker.Formula
import Checker.Modal
import Checker.Proof
import Checker.PrettyPrint

proof1a :: Proof String
proof1a = [
        Tautology $ p .->. (q .->. p),
        Generalize $ p .->. (q .->. p),
        K "p" "r",
        Substitution (fk "p" "r") [("r", q .->. p)],
        ModusPonens (fbox $ p .->. (q .->. p)) (fbox p .->. fbox (q .->. p))
    ]
    where p = fvar "p"
          q = fvar "q"

proof1b :: Proof String
proof1b = [
    ]
    where p = fvar "p"
          q = fvar "q"

printIfCorrect :: Proof String -> IO ()
printIfCorrect p = if checkProof p then putStrLn $ printProof p else putStrLn "Incorrect proof."

main :: IO ()
main = do
    printIfCorrect proof1a
    printIfCorrect proof1b

