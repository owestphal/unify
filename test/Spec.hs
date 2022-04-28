import Test.Hspec

import Examples

import Data.Maybe (isJust)
import Unify

main :: IO ()
main = hspec $ do
  describe "structural unification" $ do
    it "problem1 is solvable" $  solveProblem "i)" problem1 `shouldSatisfy` (isJust . fst)
    it "problem2 is unsolvable" $  solveProblem "ii)" problem2 `shouldNotSatisfy` (isJust . fst)
    it "problem3 is solvable" $  solveProblem "iii)" problem3 `shouldSatisfy` (isJust . fst)
    it "problem4 is solvable" $  solveProblem "iv)" problem4 `shouldSatisfy` (isJust . fst)
    it "problem5 is unsolvable" $  solveProblem "v)" problem5 `shouldNotSatisfy` (isJust . fst)

  describe "monoid unification" $ do
    fit "" $ unifyE mtheory (mproblem1 200) `shouldSatisfy` (isJust . fst)
