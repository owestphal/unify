{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant lambda" #-}
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
  unifyEWithLog,
  monoidTheory,
  Theory,
  RewriteRule,
  substitute,
  ) where

import Control.Monad.Trans.Writer
import Control.Arrow (first)

import Data.List (nub)

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Maybe
import Data.Tuple (swap)
import Data.Bifunctor (bimap)

-- -------------------------------------------
-- -------------- types ----------------------
-- -------------------------------------------
type UnificationProblem = Set (Term,Term)

newtype VarName = MkVN { name :: String } deriving (Eq,Ord)

varName :: String -> VarName
varName = MkVN

data FunctionSymbol = MkFS String Int deriving (Eq,Ord)

fsym :: String -> Int -> FunctionSymbol
fsym = MkFS

symbol :: FunctionSymbol -> String
symbol (MkFS f _) = f

arity :: FunctionSymbol -> Int
arity (MkFS _ i) = i

data Term = V VarName
          | T FunctionSymbol [Term]
          | IllDefinedTerm String
            deriving (Eq,Ord)

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

type Substitution = Set (VarName, Term)

substitute :: Substitution -> Term -> Term
substitute s (V x) = foldr (\(v,t) u -> if v == x then t else u) (V x) s
substitute s (T f xs) = T f (map (substitute s) xs)
substitute _ (IllDefinedTerm s) = IllDefinedTerm s

varsT :: Term -> Set VarName
varsT (V x) = Set.singleton x
varsT (T _ xs) = Set.unions $ map varsT xs
varsT (IllDefinedTerm _) = Set.empty

varsU :: UnificationProblem -> Set VarName
varsU = Set.foldr (\(s,t) vs -> Set.unions [varsT s, varsT t, vs]) Set.empty

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
trySolve xs | isSolvedForm xs = Just $ Set.map (\(V x,t) -> (x,t)) xs
            | otherwise       = Nothing

isSolvedForm :: UnificationProblem -> Bool
isSolvedForm xs = all solvedForm xs
  where solvedForm (V x,t) = x `notElem` varsT t
                          && x `notElem` varsU (Set.delete (V x, t) xs)
        solvedForm _ = False

isUnsolvable :: UnificationProblem -> Bool
isUnsolvable = any conflict where
  conflict (T f _,T g _) = f /= g
  conflict _ = False


-- ---------------------------------------------------------
-- ----------- Transformation operations -------------------
-- ---------------------------------------------------------
delete :: UnificationProblem -> (UnificationProblem, Maybe (Term,Term))
delete = matchAndCombine match combine
  where match (s,t) = s == t
        combine _ xs = xs


reduceTerm :: UnificationProblem -> (UnificationProblem, Maybe (Term,Term))
reduceTerm = matchAndCombine match combine
  where match (T f _, T g _) = f == g
        match _ = False
        combine (T _ ss, T _ ts) xs = xs `Set.union` Set.fromList (zip ss ts)
        combine _  _ = undefined


exchange :: UnificationProblem -> (UnificationProblem, Maybe (Term,Term))
exchange = matchAndCombine match combine
  where match (t, V _) = not $ isVar t
        match _ = False
        combine (t, V x) xs = Set.unions [xs, Set.singleton (V x, t)]
        combine _ _ = undefined

reduceVar :: UnificationProblem -> (UnificationProblem, Maybe (Term,Term))
reduceVar xs = matchAndCombine match combine xs
  where match (V x, t) = x `notElem` varsT t && x `elem` varsU (Set.delete (V x, t) xs)
        match _ = False
        combine (V x, t) ys = let sigma = substitute $ Set.singleton (x, t)
                              in Set.insert (V x,t) $ Set.map (bimap sigma sigma) ys
        combine _ _ = undefined

-- traverses a set until an element satisfies the match function.
-- then the matched element and all other elements
-- are combined using the combine function
matchAndCombine :: Ord a => (a -> Bool) -> (a -> Set a -> Set a) -> Set a -> (Set a,Maybe a)
matchAndCombine match combine xs = applyCombine $ Set.foldr f (Set.empty,Nothing) xs
  where
    applyCombine (s,Just x) = (combine x s,Just x)
    applyCombine (s,Nothing) = (s,Nothing)
    f e (s,Just x) = (Set.insert e s, Just x)
    f e (s,Nothing)
      | match e = (s,Just e)
      | otherwise = (Set.insert e s, Nothing)

-- ---------------------------------------------------------
-- ---------- Unification modulo monoids -------------------
-- ---------------------------------------------------------
unifyE ::Theory -> UnificationProblem -> Maybe Unifier
unifyE [] = unify
unifyE theory = fst . unifyEWithLog theory

unifyEWithLog :: Theory -> UnificationProblem -> (Maybe Unifier,[String])
unifyEWithLog theory up = first (fmap (Set.filter (\(x,_) -> x `elem` varsU up))) . runWriter $ unify' [up]
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
      ((s, t), up') <- selectAll up ++ selectAll (Set.map swap up),
      topSym l == topSym s]
  in applyParamodulation <$> xs
  where
    topSym (T (MkFS f _) _) = Just f
    topSym _ = Nothing


selectAll :: Ord a => Set a -> [(a,Set a)]
selectAll s = map (\e -> (e,Set.delete e s)) $ Set.toList s

data ParaChoice = ParaChoice { _rule :: RewriteRule, _equation :: (Term,Term), _restProblem :: UnificationProblem }

applyParamodulation :: ParaChoice -> UnificationProblem
applyParamodulation (ParaChoice (l,r) (s,t) up) = Set.unions [Set.fromList $ zip ls ss, Set.singleton (r',t), up]
  where
    Just (_,ls) = unApply l'
    Just (_,ss) = unApply s
    (l',r') =
      let
        upNames = Set.unions [varsT s, varsT t,varsU up]
        eqNames = varsT l `Set.union` varsT r
        freshNames = map V $ filter (`notElem` upNames) (map MkVN names)
        (freshSubst,_) = Set.foldr (\e (sub,x:xs) -> (Set.insert (e,x) sub,xs)) (Set.empty,freshNames) eqNames
      in (substitute freshSubst l, substitute freshSubst r)

names :: [String]
names = letters ++ ((++) <$> names <*> letters )
  where letters = map (:[]) ['A'..'Z']
