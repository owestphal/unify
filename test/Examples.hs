{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Examples where

import Unify

import           Control.Monad
import           Control.Monad.Trans.Writer

solveProblems :: IO ()
solveProblems = zipWithM_ f ["i)","ii)","iii)","iv)","v)"] [problem1, problem2, problem3, problem4, problem5]
  where
    f n p = do
      putStrLn $ unlines $ snd $ solveProblem n p

solveProblem :: String -> UnificationProblem -> (Maybe Unifier,[String])
solveProblem name xs = runWriter $ tell ["Solving problem " ++ name ++ ":", show xs, ""] >> unifyWithLog xs

-- ----------------------------------------
-- ------------- problems ----------------
-- ---------------------------------------
f,g,h :: _ -> Term
a,x0,x1,x2,x3,x4,y0,y1,y2,y3 :: Term
(f, g, h, a) = (term (fsym "f" 2), term (fsym "g" 5), term (fsym "h" 1), term (fsym "a" 0) [])
(x0, x1, x2, x3, x4) = (var "x0", var "x1", var "x2", var "x3", var "x4")
(y0, y1, y2, y3) = (var "y0", var "y1", var "y2", var "y3")

t1,t2,t3,t4,t5,t6,t7,t8,t9,t10 :: Term
problem1,problem2,problem3,problem4,problem5 :: UnificationProblem
t1 = f [h [x1], f [x3, x4]]
t2 = f [x2, f [x4, x2]]
t3 = f [x3, f [x2, x3]]

problem1 = [(t1,t2),(t1,t3)]

t4 = f [x1, f [x2, x3]]

problem2 = [(t1,t2),(t1,t4)]

t5 = g [x1, x2, f [y0, y0], f [y1, y1], f [y2, y2]]
t6 = g [f [x0, x0], f [x1, x1], y1, y2, x2]

problem3 = [(t5,t6)]

t7 = g [g [x1, f [x1, a], x2, x2, x3], f [a, x2], x1, x2, f [x2, a]]
t8 = g [g [x2, x4, x1, x2, f [x4, x1]], f [x1, a], x1, x2, f [a, x1]]

problem4 = [(t7,t8)]

t9  = g [x2, x1, f [a, y3], f [y1,y1], f [y2,y2]]
t10  = g [f [x0, x0], y1, f [x1, x1], x2, y3]

problem5 = [(t9,t10)]

-- ---------------------------------------
-- --------- monoid problems -------------
-- ---------------------------------------

mproblem1 :: Int -> UnificationProblem
mproblem1 n = [(cons (var "X1") (toTerm (replicate n 'a') (cons (var "X2") (toTerm "b" (constant "b")))) , toTerm ("hollo"++ replicate n 'a' ++ "cc") (toTerm "!b" (constant "b")))]
  where
    cons x y = term (fsym "cons" 2) [x,y]
mtheory :: Theory
mtheory = monoidTheory (fsym "cons" 2) (fsym "" 0)

toTerm :: String -> Term -> Term
toTerm s t = foldr (\c t -> term (fsym "cons" 2) [constant [c],t]) t s
