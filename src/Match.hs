module Match (
  match, matchE
  ) where

import           Data.List                  (nub, union)
import           Data.Tuple                 (swap)

import           Unify
import qualified Data.Set as Set
import Data.Bifunctor (second)

type Matcher = Substitution

match :: (Term,Term) -> Maybe Matcher
match = matchE []

matchE :: Theory -> (Term,Term) -> Maybe Matcher
matchE theory (s,t) = Set.map (second inverseReplace) <$> unifyE theory (Set.singleton (s,replace t))
  where
    (replace,inverseReplace) = varsToFreshConst (Set.toList $ varsT t) freshSymbols
    usedSymbols = map symbol $ symbols s `union` symbols t
    freshSymbols = filter (`notElem` usedSymbols) names

-- creates a bijective mapping from variables (in the first list)
-- to function symbols of arity 0 (with names from the second list)
-- and its inverse.
-- returns two functions to apply these mappings to terms
-- note: at least one of the lists should be finite
varsToFreshConst :: [VarName] -> [String] -> (Term -> Term, Term -> Term)
varsToFreshConst vs fs = (replace,inverseReplace)
  where mapping = zip (nub vs) (map (\s-> fsym s 0) $ nub fs)
        inverseMapping = map swap mapping
        replace = substitute (Set.fromList $ map (\(x,s)->(x,term s [])) mapping)
        inverseReplace t =
          case unApply t of
            Just (f,[]) -> case lookup f inverseMapping of
                             Just x -> var (name x)
                             Nothing -> term f []
            Just (f,ts) -> term f (map inverseReplace ts)
            Nothing -> t

names :: [String]
names = letters ++ ((++) <$> names <*> letters )
  where letters = map (:[]) ['a'..'z']
