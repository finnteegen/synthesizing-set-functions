{-# OPTIONS_FRONTEND -W no-incomplete-patterns #-}

-- This is an example for the synthesis of set functions
-- taken from the WFLP'18 paper.

module Anyof where

import Test.Prop
import ST

--------------------------------------------------------------------------------

anyOf :: [a] -> a
anyOf (x:xs) = x ? anyOf xs

--------------------------------------------------------------------------------

-- Translation of anyOf into a uniform function:
anyOfu :: [a] -> a
anyOfu []     = failed
anyOfu (x:xs) = x ? anyOf xs

-- Its plural function:
anyOfP :: IDSupply -> Int -> ST (STList Int) -> ST Int
anyOfP s l = applyST $ \xs ->
  case xs of Nil       -> Fail l
             Cons y ys -> Choice l (uniqueID s) y (anyOfP (leftSupply s) l ys)

-- The set function:
anyOfS :: [Int] -> Values Int
anyOfS x =
  fromST_Int_Int (anyOfP initSupply 1 (toST_List_STList toST_Int_Int x))

--------------------------------------------------------------------------------
-- Tests:
propS0, propS1, propS2, propS3, propS4, propS5, propS6, propS7, propS8, propS9
  :: Prop
propS0 = failing $ anyOfS failed
propS1 = anyOfS [failed] -=- []
propS2 = anyOfS [] -=- []
propS3 = anyOfS [1,2] -=- [1,2]
propS4 = anyOfS (1:failed) -=- [1]
propS5 = anyOfS [1,failed] -=- [1]
propS6 = always $ not (null (anyOfS [1,failed]))
propS7 = anyOfS [1?2,3] <~> ([1,3] ? [2,3])
propS8 = anyOfS ([1,2,3] ? [4,5,6]) <~> ([1,2,3] ? [4,5,6])
propS9 = always $ not (null (anyOfS [1..]))

