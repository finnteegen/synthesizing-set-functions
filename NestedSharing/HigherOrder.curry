{-# OPTIONS_FRONTEND -W no-incomplete-patterns #-}

-- This program tells whether an integer can be obtained
-- from an expression made up of 4 occurrences of 10 combined
-- with arithmetic operations and parentheses.
--
-- E.g., 1 = (10 - 10) + 10 / 10
-- and   2 = 10 / 10 + 10 / 10
--
-- The solution can be easily generalized to any set of numbers.

module HigherOrder where

import List
import Sort
import qualified SetFunctions as SF
import Test.Prop
import ST

--------------------------------------------------------------------------------

init :: [Int]
init = [10,10,10,10]

op :: Int -> Int -> Int
op = (+) ? (-) ? (*) ? safediv

safediv :: Int -> Int -> Int
safediv x y | y /= 0 = x `div` y

split :: [a] -> ([a], [a])
split (x:xs) = let (as,bs) = split xs in ([], x:xs) ? (x:as, bs)

ten :: [Int] -> Int
ten xs@(_:_:_) | not (null as) && not (null bs) = op (ten as) (ten bs)
 where (as, bs) = split xs
ten [x] = x

ten'set :: [Int]
ten'set = nub (SF.sortValues (SF.set1 ten init))

-- Version parameterized by the operators.
-- Therefore, the higher-order is not encapsulated.
tenh :: (Int -> Int -> Int) -> [Int] -> Int
tenh op' xs@(_:_:_) | not (null as) && not (null bs) = op' (ten as) (ten bs)
 where (as, bs) = split xs
tenh _ [x] = x

tenh'set :: [Int]
tenh'set = nub (SF.sortValues (SF.set2 tenh ((+) ? (-) ? (*)) init))

--------------------------------------------------------------------------------

nilP :: ST (STList a)
nilP = Val Nil

consP :: ST a -> ST (STList a) -> ST (STList a)
consP x xs = Val (Cons x xs)

pairP :: ST a -> ST b -> ST (STPair a b)
pairP x y = Val (Pair x y)

ifP :: ST Bool -> ST a -> ST a -> ST a
ifP sb st se = applyST (\b -> if b then st else se) sb

eqP :: Eq a => ST a -> ST a -> ST Bool
eqP = lift2P (==)

notP :: ST Bool -> ST Bool
notP = lift1P not

andP :: ST Bool -> ST Bool -> ST Bool
andP fx fy = applyST (\x -> case x of False -> Val False
                                      _     -> fy) fx

nullP :: ST (STList a) -> ST Bool
nullP =  applyST $ \xs -> case xs of Nil -> Val True
                                     Cons _ _ -> Val False

plusP, minusP, multP, safedivP :: IDSupply -> Int -> ST Int -> ST Int -> ST Int
plusP _ _ = lift2P (+)
minusP _ _ = lift2P (-)
multP _ _ = lift2P (*)
safedivP _ l sx sy = ifP (notP (eqP sy (Val 0))) (lift2P div sx sy) (Fail l)

fstP :: ST (STPair a b) -> ST a
fstP = applyST $ \ (Pair sa _) -> sa

sndP :: ST (STPair a b) -> ST b
sndP = applyST $ \ (Pair _ sb) -> sb

opP :: IDSupply -> Int -> ST (IDSupply -> Int -> ST Int -> ST Int -> ST Int)
opP s l = Choice l i1 (Val plusP)
                      (Choice l i2 (Val minusP)
                                   (Choice l i3 (Val multP) (Val safedivP)))
  where i1 = uniqueID (leftSupply s)
        i2 = uniqueID (leftSupply (rightSupply s))
        i3 = uniqueID (rightSupply (rightSupply s))

splitP :: IDSupply -> Int -> ST (STList a) -> ST (STPair (STList a) (STList a))
splitP s l = applyST $ \xs -> case xs of
  Cons sx sxs -> let sp  = splitP (leftSupply s) l sxs
                     sas = fstP sp
                     sbs = sndP sp
                 in Choice l (uniqueID s) (pairP nilP (consP sx sxs))
                                          (pairP (consP sx sas) sbs)
  Nil -> Fail l

tenP :: IDSupply -> Int -> ST (STList Int) -> ST Int
tenP s l = applyST $ \xs -> case xs of
  Cons sy sys -> applyST (\ys -> case ys of
    Cons _ _ -> let sp  = splitP s1 l (Val xs)
                    sas = fstP sp
                    sbs = sndP sp
                in ifP (andP (notP (nullP sas)) (notP (nullP sbs)))
                       (applyST (\op' -> op' s5 l (tenP s2 l sas)
                                                  (tenP s3 l sbs))
                                (opP s4 l))
                       (Fail l)
    Nil -> sy) sys
  Nil -> Fail l
 where s1 = leftSupply s
       s2 = leftSupply (rightSupply s)
       s3 = leftSupply (rightSupply (rightSupply s))
       s4 = leftSupply (rightSupply (rightSupply (rightSupply s)))
       s5 = rightSupply (rightSupply (rightSupply (rightSupply s)))

tenS :: [Int] -> Values Int
tenS xs = fromST_Int_Int (tenP initSupply 1 (toST_List_STList toST_Int_Int xs))

ten'set' :: [Int]
ten'set' = nub (sort (tenS init))

-- Version parameterized by the operators.
-- Therefore, the higher-order is not encapsulated.
tenhP :: IDSupply -> Int -> ST (IDSupply -> Int -> ST Int -> ST Int -> ST Int)
      -> ST (STList Int) -> ST Int
tenhP s l sop = applyST $ \xs -> case xs of
  Cons sy sys -> applyST (\ys -> case ys of
    Cons _ _ -> let sp  = splitP s1 l (Val xs)
                    sas = fstP sp
                    sbs = sndP sp
                in ifP (andP (notP (nullP sas)) (notP (nullP sbs)))
                       (applyST (\op' -> op' s4 l (tenP s2 l sas)
                                                  (tenP s3 l sbs))
                                sop)
                       (Fail l)
    Nil -> sy) sys
  Nil -> Fail l
 where s1 = leftSupply s
       s2 = leftSupply (rightSupply s)
       s3 = leftSupply (rightSupply (rightSupply s))
       s4 = leftSupply (rightSupply (rightSupply (rightSupply s)))

tenhS :: (IDSupply -> Int -> ST Int -> ST Int -> ST Int) -> [Int] -> Values Int
tenhS fP xs = fromST_Int_Int
  (tenhP initSupply 1 (Uneval fP) (toST_List_STList toST_Int_Int xs))

tenh'set' :: [Int]
tenh'set' = nub (sort (tenhS (plusP ? minusP ? multP) init))

--------------------------------------------------------------------------------

-- Tests:
test1, test2 :: Prop
test1 = ten'set -=- [-990,-900,-190,-100,-99,-90,-80,-20,-19,-10,-9,-8,-2,-1
                    ,0,1,2,3,5,8,9,10,11,12,19,20,21,40,80,90,99,100,101,110
                    ,120,190,200,210,300,400,900,990,1010,1100,2000,10000]
test2 =
  tenh'set <~> ([-80,0,1,2,10,12,19,20,21,40,100,101,120,200,210,1010] ?
                [-990,-190,-100,-99,-80,-20,-19,-10,-8,-1
                ,0,1,8,10,19,20,80,99,100,190,990] ?
                [-900,-100,-90,0,1,20,90,100,110,300,400,900,1100,2000,10000])

