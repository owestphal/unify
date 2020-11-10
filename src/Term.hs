{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
module Term where

import Data.List

import GHC.TypeLits

-- API
functionSymbol :: Int -> String -> FunctionSymbol
functionSymbol = (,)

signature :: [FunctionSymbol] -> Signature
signature xs = foldr f l xs
  where l = replicate (m+1) []
        m = maximum [ b | (b,_) <- xs ]
        f (n,s) yss = let (front, fs:back) = splitAt n yss
                     in front ++ (s:fs) : back

useSignature :: Signature -> TermDef s
useSignature xs = TermDef { var = Var
                          , compose = compose' }
  where compose' (n,s) ts | s `elem` (xs !! n) && length ts == n = Term (n,s) ts
                          | s `notElem` (xs !! n) = error "functionsymbol not in signature"
                          | otherwise = error "wrong number of subterms"


data TermDef (s :: TSignature) = TermDef
                              { var :: String -> Term s
                              , compose :: FunctionSymbol -> [Term s] -> Term s }

type Equation a = (Term a, Term a)
type Rule a = (Term a,Term a)
type TRS a = [Rule a]

-- internals
data Term (s :: TSignature) where
  Var :: String -> Term s
  Term  :: FunctionSymbol -> [Term s] -> Term s


type FunctionSymbol = (Int, String)
type Signature = [[String]]

data TSignature

-- ------------------
-- functions on terms
-- ------------------

-- --------
-- examples
-- --------
sig = signature [(0,"O"),(2,"plus"),(1,"succ"),(2,"times")]
TermDef {var = v, compose = c} = useSignature sig
t = c (2,"plus") [v "x", c (0,"O") []]

sig' = signature [(0,"a"),(1,"f")]
TermDef {var = v', compose = c'} = useSignature sig'
