{-# OPTIONS_FRONTEND -W no-incomplete-patterns #-}

module NestedSharing where

import Sort
import qualified SetFunctions as SF
import Test.Prop
import ST

--------------------------------------------------------------------------------

type Doc = [Entry]
type Entry = [Attr]
type Attr = (Int, Int)

e1, e2, e3 :: Entry
e1 = [(0, 1), (1, 2)]
e2 = [(0, 2), (1, 2), (1, 2)]
e3 = [(0, 3)]

doc :: Doc
doc = [e1, e2, e3]

lookup :: Eq a => a -> [(a, b)] -> b
lookup k ((k',v):kvs) = (if k == k' then v else failed) ? lookup k kvs

zero :: Entry -> Int
zero e = lookup 0 e

one :: Entry -> Int
one e = lookup 1 e

oneCount :: Doc -> (Int, Int)
oneCount d = let e = anyOf d in (zero e, length $ SF.sortValues $ SF.set1 one e)

getOneCounts :: Doc -> [(Int, Int)]
getOneCounts = SF.sortValues . SF.set1 oneCount

--------------------------------------------------------------------------------

type STDoc = STList STEntry
type STEntry = STList STAttr
type STAttr = STPair Int Int

nilP :: ST (STList a)
nilP = Val Nil

consP :: ST a -> ST (STList a) -> ST (STList a)
consP x xs = Val (Cons x xs)

pairP :: ST a -> ST b -> ST (STPair a b)
pairP x y = Val (Pair x y)

lengthP :: ST (STList a) -> ST Int
lengthP = applyST $ \xs -> case xs of Nil -> Val 0
                                      Cons _ sxs -> plusP (Val 1) (lengthP sxs)

ifP :: ST Bool -> ST a -> ST a -> ST a
ifP sb st se = applyST (\b -> if b then st else se) sb

eqP :: Eq a => ST a -> ST a -> ST Bool
eqP = lift2P (==)

plusP :: Num a => ST a -> ST a -> ST a
plusP = lift2P (+)

lookupP :: IDSupply -> Int -> ST Int -> ST (STList (STPair Int Int)) -> ST Int
lookupP s l sk = applyST $ \xs -> case xs of
  Nil         -> Fail l
  Cons sx sxs -> Choice l (uniqueID s)
    (applyST (\x -> case x of Pair sa sb -> ifP (eqP sk sa) sb (Fail l)) sx)
    (lookupP (leftSupply s) l sk sxs)

anyOfP :: IDSupply -> Int -> ST (STList a) -> ST a
anyOfP s l = applyST $ \xs -> case xs of
  Nil         -> Fail l
  Cons sx sxs -> Choice l (uniqueID s) sx (anyOfP (leftSupply s) l sxs)

zeroP :: IDSupply -> Int -> ST STEntry -> ST Int
zeroP s l = lookupP s l (Val 0)

oneP :: IDSupply -> Int -> ST STEntry -> ST Int
oneP s l = lookupP s l (Val 1)

oneSP :: IDSupply -> Int -> ST STEntry -> ST (STList Int)
oneSP s l se = stValuesP (l+1) (oneP s (l+1) se)

oneCountP :: IDSupply -> Int -> ST STDoc -> ST (STPair Int Int)
oneCountP s l sd = let se = anyOfP s1 l sd
                   in pairP (zeroP s2 l se) (lengthP $ oneSP s3 l se)
 where s1 = leftSupply s
       s2 = leftSupply (rightSupply s)
       s3 = rightSupply (rightSupply s)

oneCountS :: Doc -> Values (Int, Int)
oneCountS d = fromST_Pair_STPair fromValST_Int_Int fromValST_Int_Int
  (oneCountP initSupply 1 (toST_List_STList (toST_List_STList
    (toST_Pair_STPair toST_Int_Int toST_Int_Int)) d))

getOneCounts' :: Doc -> [(Int, Int)]
getOneCounts' = sort . oneCountS

--------------------------------------------------------------------------------

-- Test:
test :: Prop
test = getOneCounts doc -=- getOneCounts' doc
