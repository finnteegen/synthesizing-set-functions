module Nested where

-- An example for nested set functions showing a difference in the
-- current implementations of set functions in PAKCS and KiCS2.

import qualified SetFunctions as SF
import Test.EasyCheck
import ST

--------------------------------------------------------------------------------

f1 :: Bool -> Bool
f1 x = x ? True

m1 :: [Bool] -> SF.Values Bool
m1 xs = SF.set1 f1 (head xs)
-- Note that (m1 []) yields the set {True} according to the semantics
-- of nested set functions defined in [Christiansen et al. PPDP 2013].
-- However, the implementation of set function in PAKCS fails on this
-- expression due to its incomplete implementation of nested set functions.

m11 :: Bool
m11 = SF.isEmpty (SF.set1 m1 [])
-- m11 yields False in KiCS2 (according to [Christiansen et al. PPDP 2013]).
-- m11 yields True in PAKCS.

f2 :: Bool -> Bool
f2 x = x ? failed

m2 :: [Bool] -> SF.Values Bool
m2 xs = SF.set1 f2 (head xs)
-- Note that (m2 []) yields the empty set according to the semantics
-- of nested set functions defined in [Christiansen et al. PPDP 2013].
-- However, the implementation of set function in PAKCS fails on this
-- expression due to its incomplete implementation of nested set functions.

m22 :: Bool
m22 = SF.isEmpty (SF.set1 m2 [])
-- Since (m2_S []) evaluates to a set containing an empty set as an element,
-- m22 yields False in KiCS2 (according to [Christiansen et al. PPDP 2013]).
-- m22 yields True in PAKCS.

--------------------------------------------------------------------------------

-- Plural function of `f1`:
f1P :: Int -> ST Bool -> ST Bool
f1P l x = Choice l x (Val True)

-- Plural function of the set function of `f1`:
f1SP :: Int -> ST Bool -> ST (STList Bool)
f1SP l = stValuesP (l+1) . f1P (l+1)

-- Plural function of `head`:
headP :: Int -> ST (STList a) -> ST a
headP l = applyST $ \xs -> case xs of Nil      -> Fail l
                                      Cons x _ -> x

-- Plural function of `m1`:
m1P :: Int -> ST (STList Bool) -> ST (STList Bool)
m1P l xs = f1SP l (headP l xs)

-- Set function of `m1`:
m1S :: [Bool] -> Values [Bool]
m1S x = fromST_List_STList fromValST_Bool_Bool
  (m1P 1 (toST_List_STList toST_Bool_Bool x))

m11' :: Bool
m11' = null (m1S [])

-- Plural function of `f2`:
f2P :: Int -> ST Bool -> ST Bool
f2P l x = Choice l x (Fail l)

-- Plural function of the set function of `f2`:
f2SP :: Int -> ST Bool -> ST (STList Bool)
f2SP l = stValuesP (l+1) . f2P (l+1)

-- Plural function of `m2`:
m2P :: Int -> ST (STList Bool) -> ST (STList Bool)
m2P l xs = f2SP l (headP l xs)

-- Set function of `m2`:
m2S :: [Bool] -> Values [Bool]
m2S x = fromST_List_STList fromValST_Bool_Bool
  (m2P 1 (toST_List_STList toST_Bool_Bool x))

m22' :: Bool
m22' = null (m2S [])

--------------------------------------------------------------------------------

-- Tests:
test1, test2 :: Prop
test1 = m11' -=- False
test2 = m22' -=- False

