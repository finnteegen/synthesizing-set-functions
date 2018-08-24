module NDConst where

-- This program demonstrates the lazy evaluation of set functions
-- and is taken from the WFLP'18 paper.

import qualified SetFunctions as SF
import Test.Prop
import ST

--------------------------------------------------------------------------------

ndconst :: Int -> Int -> Int
ndconst x _ = x ? 1

main1, main2, main3 :: SF.Values Int
main1 = SF.set2 ndconst 2 failed
main2 = SF.set2 ndconst (2?4) failed
main3 = SF.set2 ndconst 2 (1?3)

--------------------------------------------------------------------------------

-- Plural function:
ndconstP :: Int -> ST Int -> ST Int -> ST Int
ndconstP l nx _ = (\x -> Choice l (Val x) (Val 1)) `applyST` nx

-- Set function:
ndconstS :: Int -> Int -> Values Int
ndconstS x y = fromST_Int_Int (ndconstP 1 (toST_Int_Int x) (toST_Int_Int y))

--------------------------------------------------------------------------------

-- Tests:
test1, test2, test3 :: Prop
test1 = ndconstS 2 failed -=- [2,1]
test2 = ndconstS (2?4) failed <~> ([2,1] ? [4,1])
test3 = ndconstS 2 (1?3) -=- [2,1]
