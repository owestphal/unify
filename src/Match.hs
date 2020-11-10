module Match where

import           Data.List                  (nub, union)
import           Data.Maybe                 (fromMaybe)
import           Data.Tuple                 (swap)

import           Control.Monad.Trans.Writer (runWriter)

import           Unify

type Matcher = Substitution

match :: TermPair -> Maybe Matcher
match (s,t) = fmap (map (\(x,t) -> (x,inverseReplace t))) $ fst.runWriter $ unify [(s,replace t)]
  where (replace,inverseReplace) = varsToFreshConst (varsT t) freshSymbols
        usedSymbols = map (\(MkFS f _) -> f) $ symbols s `union` symbols t
        freshSymbols = filter (`notElem` usedSymbols) names

-- creates a bijective mapping from variables (in the first list)
-- to function symbols of arity 0 (with names from the second list)
-- and its inverse.
-- returns two functions to apply these mappings to terms
-- note: at least one of the lists should be finite
varsToFreshConst :: [VarName] -> [String] -> (Term -> Term, Term -> Term)
varsToFreshConst vs fs = (replace,inverseReplace)
  where mapping = zip (nub vs) (map (\s-> MkFS s 0) $ nub fs)
        inverseMapping = map swap mapping
        replace = substitute (map (\(x,s)->(x,term s [])) mapping)
        inverseReplace (V x) = V x
        inverseReplace (T f []) = case lookup f inverseMapping of
                             Just x -> V x
                             Nothing -> T f []
        inverseReplace (T f ts) = T f (map inverseReplace ts)
        inverseReplace (IllDefinedTerm s) = IllDefinedTerm s

symbols :: Term -> [FunctionSymbol]
symbols (V _) = []
symbols (T f ts) = nub $ f : concatMap symbols ts
symbols (IllDefinedTerm _) = []

names :: [String]
names = letters ++ ((++) <$> names <*> letters )
  where letters = map (:[]) ['a'..'z']
