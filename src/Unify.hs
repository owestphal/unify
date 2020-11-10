module Unify where

import           Control.Monad
import           Control.Monad.Trans.Writer
import qualified Data.List                  as List
import           Data.Maybe

-- -------------------------------------------
-- -------------- types ----------------------
-- -------------------------------------------
type TermPair = (Term,Term)
type UnificationProblem = [TermPair]

newtype VarName = MkVN String deriving Eq
data FunctionSymbol = MkFS String Int deriving Eq

data Term = V VarName
          | T FunctionSymbol [Term]
          | IllDefinedTerm String
            deriving Eq

-- smart constructo for T
term :: FunctionSymbol -> [Term] -> Term
term f@(MkFS _ i) xs = if length xs == i
                      then T f xs
                      else IllDefinedTerm $ "wrong number of arguments in " ++ show f

-- "smart" constructor for V, for consistence
var :: VarName -> Term
var = V

-- ----------------------------------------
-- -------- Show instances ----------------
-- ----------------------------------------
instance Show FunctionSymbol where
  show (MkFS f _) = f

instance Show VarName where
  show (MkVN x) = x

instance Show Term where
  show (V x) = show x
  show (T f []) = show f
  show (T f xs) = show f ++ show xs
  show (IllDefinedTerm xs) = xs

-- -------------------------------------------
-- ----- some needed functions on terms ------
-- -------------------------------------------
isVar :: Term -> Bool
isVar (V _) = True
isVar _     = False

type Substitution = [(VarName, Term)]

substitute :: Substitution -> Term -> Term
substitute [] (V x) = V x
substitute ((v,t):ss) (V x) | v == x = t
                            | otherwise = substitute ss (V x)
substitute s (T f xs) = T f (map (substitute s) xs)
substitute _ (IllDefinedTerm s) = IllDefinedTerm s

varsT :: Term -> [VarName]
varsT (V x) = [x]
varsT (T _ xs) = List.nub $ concatMap varsT xs
varsT (IllDefinedTerm _) = []

varsU :: UnificationProblem -> [VarName]
varsU xs = List.nub $ [ x | (s,_) <- xs, x <- varsT s] ++ [ x | (_,t) <- xs, x <- varsT t]

-- ---------------------------------------------
-- -------------- unification ------------------
-- ---------------------------------------------
type Unifier = Substitution

unify :: UnificationProblem -> Writer [String] (Maybe Unifier)
unify xs = do
  ys <- unificationStep delete      (logString "Delete") xs
    >>= unificationStep reduceTerm  (logString "Term reduction")
    >>= unificationStep exchange    (logString "Swap")
    >>= unificationStep reduceVar   (logString "Variable reduction")

  if xs == ys
    then do
      tell ["No further rule applicable."]
      let maybeSolution = trySolve ys
      if isNothing maybeSolution then tell ["No unifier found!"] else tell ["Found unifier!"]
      return maybeSolution
    else unify ys

logString :: String -> (Term,Term) -> String
logString msg (s,t) = concat [msg, ": (", show s, ", ", show t, ")"]

type UnificationStep = UnificationProblem -> (UnificationProblem, Maybe TermPair)

-- this function takes care of applying the reduction steps
-- and the logging based on the outcome of the reduction step
unificationStep :: UnificationStep
                -> (TermPair -> String)
                ->  UnificationProblem
                -> Writer [String] UnificationProblem
unificationStep step logMsg xs = case step xs of
                      (ys, Just pair) -> writer (ys, [logMsg pair, "new problem: "++ show ys, "" ])
                      (ys, Nothing) -> writer (ys, [])

trySolve :: UnificationProblem -> Maybe Unifier
trySolve xs | isSolvedForm xs = Just $ map (\(V x,t) -> (x,t)) xs
            | otherwise       = Nothing

isSolvedForm :: UnificationProblem -> Bool
isSolvedForm xs = all solvedForm xs
  where solvedForm (V x,t) = x `notElem` varsT t
                          && x `notElem` varsU (List.delete (V x, t) xs)
        solvedForm _ = False

-- ---------------------------------------------------------
-- ----------- Transformation operations -------------------
-- ---------------------------------------------------------
delete :: UnificationProblem -> (UnificationProblem, Maybe TermPair)
delete = matchAndCombine match combine
  where match (s,t) = s == t
        combine xs _ ys = xs ++ ys


reduceTerm :: UnificationProblem -> (UnificationProblem, Maybe TermPair)
reduceTerm = matchAndCombine match combine
  where match (T f _, T g _) = f == g
        match _ = False
        combine xs (T _ ss, T _ ts) ys = List.nub $ xs ++ zip ss ts ++ ys
        combine _ _  _ = undefined


exchange :: UnificationProblem -> (UnificationProblem, Maybe TermPair)
exchange = matchAndCombine match combine
  where match (t, V _) = not $ isVar t
        match _ = False
        combine xs (t, V x) ys = List.nub $ xs ++ [(V x, t)] ++ ys
        combine _ _ _ = undefined

reduceVar :: UnificationProblem -> (UnificationProblem, Maybe TermPair)
reduceVar xs = matchAndCombine match combine xs
  where match (V x, t) = x `notElem` varsT t && x `elem` varsU (xs List.\\ [(V x, t)])
        match _ = False
        combine ys (V x, t) zs = let sigma = substitute [(x, t)]
                                 in (V x,t) : List.nub [(sigma u, sigma v) | (u,v) <- ys ++ zs ]
        combine _ _ _ = undefined

-- traverses a list until an element satisfies the match function.
-- then the skipped elements, the matched element, and the remaining elements
-- are rearranged/modified using the combine function
matchAndCombine :: (a -> Bool) -> ([a] -> a -> [a] -> [a]) -> [a] -> ([a],Maybe a)
matchAndCombine match combine xs = go xs []
  where go [] zs     = (zs, Nothing)
        go (y:ys) zs = if match y
                       then (combine (reverse zs) y ys, Just y)
                       else go ys (y:zs)

-- ----------------------------------------
-- ------------- problems ----------------
-- ---------------------------------------
solveProblems :: IO ()
solveProblems = zipWithM_ solveProblem ["i)","ii)","iii)","iv)","v)"] [problem1, problem2, problem3, problem4, problem5]

solveProblem :: String -> UnificationProblem -> IO ()
solveProblem name xs =
  let (_,logs) = runWriter $
                    tell ["Solving problem " ++ name ++ ":", show xs, ""]
                    >> unify xs
  in putStrLn (unlines logs)

f,g,h :: _ -> Term
a,x0,x1,x2,x3,x4,y0,y1,y2,y3 :: Term
(f, g, h, a) = (term (MkFS "f" 2), term (MkFS "g" 5), term (MkFS "h" 1), term (MkFS "a" 0) [])
(x0, x1, x2, x3, x4) = (var (MkVN "x0"), var (MkVN "x1"), var (MkVN "x2"), var (MkVN "x3"), var (MkVN "x4"))
(y0, y1, y2, y3) = (var (MkVN "y0"), var (MkVN "y1"), var (MkVN "y2"), var (MkVN "y3"))

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
