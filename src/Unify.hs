{-# LANGUAGE PartialTypeSignatures #-}
module Unify (
  UnificationProblem,
  Substitution,
  Unifier,
  Term,
  VarName,
  FunctionSymbol,
  varName,
  name,
  fsym,
  symbol,
  symbols,
  unApply,
  arity,
  term,
  var,
  constant,
  isVar,
  isIllDefined,
  varsT,
  unify,
  unifyWithLog,
  unifyE,
  monoidTheory,
  Theory,
  RewriteRule,
  substitute,
  ) where

import Control.Monad.Trans.Writer

import Data.List (nub, (\\))
import qualified Data.List as List (delete)
import Data.Maybe
import Data.Tuple (swap)
import Control.Arrow (first)

-- -------------------------------------------
-- -------------- types ----------------------
-- -------------------------------------------
type UnificationProblem = [(Term,Term)]

newtype VarName = MkVN { name :: String } deriving Eq

varName :: String -> VarName
varName = MkVN

data FunctionSymbol = MkFS String Int deriving Eq

fsym :: String -> Int -> FunctionSymbol
fsym = MkFS

symbol :: FunctionSymbol -> String
symbol (MkFS f _) = f

arity :: FunctionSymbol -> Int
arity (MkFS _ i) = i

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
var :: String -> Term
var = V . MkVN

-- constants, ie, function symbols of arity 0
constant :: String -> Term
constant c = term (fsym c 0) []

symbols :: Term -> [FunctionSymbol]
symbols (V _) = []
symbols (T f ts) = nub $ f : concatMap symbols ts
symbols (IllDefinedTerm _) = []

unApply :: Term -> Maybe (FunctionSymbol, [Term])
unApply (T f ts) = Just (f, ts)
unApply _ = Nothing

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

isIllDefined :: Term -> Bool
isIllDefined (IllDefinedTerm _) = True
isIllDefined _     = False

type Substitution = [(VarName, Term)]

substitute :: Substitution -> Term -> Term
substitute [] (V x) = V x
substitute ((v,t):ss) (V x) | v == x = t
                            | otherwise = substitute ss (V x)
substitute s (T f xs) = T f (map (substitute s) xs)
substitute _ (IllDefinedTerm s) = IllDefinedTerm s

varsT :: Term -> [VarName]
varsT (V x) = [x]
varsT (T _ xs) = nub $ concatMap varsT xs
varsT (IllDefinedTerm _) = []

varsU :: UnificationProblem -> [VarName]
varsU xs = nub $ [ x | (s,_) <- xs, x <- varsT s] ++ [ x | (_,t) <- xs, x <- varsT t]

-- ---------------------------------------------
-- -------------- unification ------------------
-- ---------------------------------------------
type Unifier = Substitution

unify :: UnificationProblem -> Maybe Unifier
unify = fst . runWriter . unifyWithLog

unifyWithLog :: UnificationProblem -> Writer [String] (Maybe Unifier)
unifyWithLog xs = do
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
    else unifyWithLog ys

logString :: String -> (Term,Term) -> String
logString msg (s,t) = concat [msg, ": (", show s, ", ", show t, ")"]

type UnificationStep = UnificationProblem -> (UnificationProblem, Maybe (Term,Term))

-- this function takes care of applying the reduction steps
-- and the logging based on the outcome of the reduction step
unificationStep :: UnificationStep
                -> ((Term,Term) -> String)
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

isUnsolvable :: UnificationProblem -> Bool
isUnsolvable [] = False
isUnsolvable ((s,t):xs) = conflict s t || isUnsolvable xs
  where
    conflict (T f _) (T g _) = f /= g
    conflict _ _ = False


-- ---------------------------------------------------------
-- ----------- Transformation operations -------------------
-- ---------------------------------------------------------
delete :: UnificationProblem -> (UnificationProblem, Maybe (Term,Term))
delete = matchAndCombine match combine
  where match (s,t) = s == t
        combine xs _ ys = xs ++ ys


reduceTerm :: UnificationProblem -> (UnificationProblem, Maybe (Term,Term))
reduceTerm = matchAndCombine match combine
  where match (T f _, T g _) = f == g
        match _ = False
        combine xs (T _ ss, T _ ts) ys = nub $ xs ++ zip ss ts ++ ys
        combine _ _  _ = undefined


exchange :: UnificationProblem -> (UnificationProblem, Maybe (Term,Term))
exchange = matchAndCombine match combine
  where match (t, V _) = not $ isVar t
        match _ = False
        combine xs (t, V x) ys = nub $ xs ++ [(V x, t)] ++ ys
        combine _ _ _ = undefined

reduceVar :: UnificationProblem -> (UnificationProblem, Maybe (Term,Term))
reduceVar xs = matchAndCombine match combine xs
  where match (V x, t) = x `notElem` varsT t && x `elem` varsU (xs \\ [(V x, t)])
        match _ = False
        combine ys (V x, t) zs = let sigma = substitute [(x, t)]
                                 in (V x,t) : nub [(sigma u, sigma v) | (u,v) <- ys ++ zs ]
        combine _ _ _ = undefined

-- traverses a list until an element satisfies the match function.
-- then the skipped elements, the matched element, and the remaining elements
-- are rearranged/modified using the combine function
matchAndCombine :: (a -> Bool) -> ([a] -> a -> [a] -> [a]) -> [a] -> ([a],Maybe a)
matchAndCombine match combine xs = go xs []
  where go [] zs     = (reverse zs, Nothing)
        go (y:ys) zs = if match y
                       then (combine (reverse zs) y ys, Just y)
                       else go ys (y:zs)

-- ---------------------------------------------------------
-- ---------- Unification modulo monoids -------------------
-- ---------------------------------------------------------
unifyE :: Theory -> UnificationProblem -> (Maybe Unifier,[String])
unifyE theory up = first (fmap (filter (\(x,_) -> x `elem` varsU up))) . runWriter $ unify' [up]
  where
    unify' :: [UnificationProblem] -> Writer [String] (Maybe Unifier)
    unify' [] = tell ["No unifier found!"] >> pure Nothing
    unify' (xs:xss) = do
      tell ["try simple rules"]
      ys <- unificationStep delete      (logString "Delete") xs
        >>= unificationStep exchange    (logString "Swap")
        >>= unificationStep reduceVar   (logString "Variable reduction")

      if xs == ys
        then do
          tell ["No further simple rules applicable."]
          let maybeSolution = trySolve ys
          if isNothing maybeSolution
            then do
              tell ["try term reduction and paramodulation"]
              zs <- unificationStep reduceTerm  (logString "Term reduction") ys
              let
                yss = paramodulations theory ys
              -- tell ["new candidates: " ++ show yss]
              let
                yss' = [zs | zs /= ys] ++ filter (not . isUnsolvable) yss
              -- tell [show (length yss') ++ " solvable candidates"]
              unify' (yss'++xss)
            else do
              tell ["Found unifier!"]
              return maybeSolution
        else do
          tell [show xs,show ys]
          unify' (ys:xss)

type Theory = [RewriteRule]
type RewriteRule = (Term,Term)

monoidTheory :: FunctionSymbol -> FunctionSymbol -> Theory
monoidTheory fSym eSym
  | arity fSym == 2 && arity eSym == 0 =
    [ (f e x, x) -- I_l
    , (f x e, x) -- I_r
    , (f (f x y) z, f x (f y z))] -- A
  | otherwise = error "arity error"
  where
    f a b = term fSym [a,b]
    e = term eSym []
    (x,y,z) = (var "A",var "B",var "C")

paramodulations :: Theory -> UnificationProblem -> [UnificationProblem]
paramodulations theory up =
  let
    xs = [ParaChoice (l, r) (s, t) up' |
      (l, r) <- theory,
      isJust $ topSym l,
      ((s, t), up') <- selectAll up ++ selectAll (map swap up),
      topSym l == topSym s]
  in applyParamodulation <$> xs
  where
    topSym (T (MkFS f _) _) = Just f
    topSym _ = Nothing


selectAll :: [a] -> [(a,[a])]
selectAll = go [] where
  go _ [] = []
  go xs (y:ys) = (y,xs++ys) : go (y:xs) ys

data ParaChoice = ParaChoice { _rule :: RewriteRule, _equation :: (Term,Term), _restProblem :: UnificationProblem }

applyParamodulation :: ParaChoice -> UnificationProblem
applyParamodulation (ParaChoice (l,r) (s,t) up) = zip ls ss ++ [(r',t)] ++ up
  where
    Just (_,ls) = unApply l'
    Just (_,ss) = unApply s
    (l',r') =
      let
        upNames = varsU $ (s,t):up
        eqNames = nub $ varsT l ++ varsT r
        freshSubst = zip eqNames $ map V $ filter (`notElem` upNames) (map MkVN names)
      in (substitute freshSubst l, substitute freshSubst r)

names :: [String]
names = letters ++ ((++) <$> names <*> letters )
  where letters = map (:[]) ['A'..'Z']
