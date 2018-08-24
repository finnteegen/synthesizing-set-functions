{-# OPTIONS_FRONTEND -W no-incomplete-patterns -W no-overlapping #-}

-- This program solves the n queens problem using set functions.

module Queens where

import Test.Prop
import ST

--------------------------------------------------------------------------------

perm :: [a] -> [a]
perm []     = []
perm (x:xs) = insert (perm xs)
 where
  insert ys     = x : ys
  insert (y:ys) = y : insert ys

unsafe :: [Int] -> Bool
-- With functional patterns:
-- unsafe (_++[x]++y++[z]++_) = abs (x-z) =:= length y + 1
-- Without functional patterns:
unsafe (x:xs) = unsafe1 x 0 xs
unsafe (_:xs) = unsafe xs

unsafe1 :: Int -> Int -> [Int] -> Bool
unsafe1 fst d (x:_ ) = abs (fst-x) =:= d+1
unsafe1 fst d (_:xs) = unsafe1 fst (d+1) xs

-- Plural functions:
ifP :: ST Bool -> ST a -> ST a -> ST a
ifP sb st se = applyST (\b -> if b then st else se) sb

eqP :: Eq a => ST a -> ST a -> ST Bool
eqP = lift2P (==)

absP :: Num a => ST a -> ST a
absP = lift1P abs

plusP, minusP :: Num a => ST a -> ST a -> ST a
plusP = lift2P (+)
minusP = lift2P (-)

unsafeP :: ST (STList Int) -> ST Bool
unsafeP = applyST $ \zs -> case zs of
  Nil       -> Fail
  Cons x xs -> Choice (unsafe1P x (Val 0) xs) (unsafeP xs)

unsafe1P :: ST Int -> ST Int -> ST (STList Int) -> ST Bool
unsafe1P fst d zs = unsafe1Case `applyST` zs
 where
  unsafe1Case Nil         = Fail
  unsafe1Case (Cons x xs) = Choice (unsafe1P fst (lift1P (+1) d) xs)
                                   (unsafeTest fst x d)
   where unsafeTest fst' x' d' =
          ifP (eqP (absP (minusP fst' x')) (plusP d' (Val 1))) (Val True)
                                                               Fail

-- Set function:
unsafeS :: [Int] -> Values Bool
unsafeS x = fromST_Bool_Bool (unsafeP (toST_List_STList toST_Int_Int x))

queens :: Int -> [Int]
queens n | null (unsafeS p) = p
 where p = perm [1..n]

--------------------------------------------------------------------------------

-- Tests:
testQueens4, testQueens6 :: Prop
testQueens4 = (queens 4) <~> ([3,1,4,2] ? [2,4,1,3])
testQueens6 = (queens 6) <~>
              ([5,3,1,6,4,2] ? [4,1,5,2,6,3] ? [3,6,2,5,1,4] ? [2,4,6,1,3,5])

