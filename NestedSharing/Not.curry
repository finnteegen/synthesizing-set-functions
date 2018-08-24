module Not where

-- An example for nested set functions taken from the WFLP'18 paper.

import qualified SetFunctions as SF
import Test.Prop
import ST

--------------------------------------------------------------------------------

not :: Bool -> Bool
not False = True
not True  = False

notf :: SF.Values Bool
notf = SF.set1 not failed

test_notf :: Prop
test_notf = failing (SF.isEmpty notf)

notfs :: SF.Values (SF.Values Bool)
notfs = SF.set0 notf

test_notfs :: Prop
test_notfs = SF.isEmpty notfs -=- True

nots :: Bool -> SF.Values Bool
nots x = SF.set1 not x

test_nots :: Prop
test_nots = failing (SF.isEmpty (nots failed))

--------------------------------------------------------------------------------

-- The plural function of `not`:
notP :: IDSupply -> Int -> ST Bool -> ST Bool
notP _ _ = applyST $ \x -> case x of False -> Val True
                                     True  -> Val False

-- To synthesize the plural function of `notf`, we need
-- the plural function of the set function of `not`:
notSP :: IDSupply -> Int -> ST Bool -> ST (STList Bool)
notSP s l x = stValuesP (l+1) (notP s (l+1) x)

-- Now we can define the plural function of `notf`:
notfP :: IDSupply -> Int -> ST (STList Bool)
notfP s l = notSP s l (Fail l)

-- The synthesized set function of `notf` (as required in `notfs`):
notfS :: Values (Values Bool)
notfS = fromST_List_STList fromValST_Bool_Bool (notfP initSupply 1)

test_notfS :: Prop
test_notfS = notfS -=- []

-- The synthesized set function of `not`:
notS :: Bool -> Values Bool
notS x = fromST_Bool_Bool (notP initSupply 1 (toST_Bool_Bool x))

-- The definion of `nots` with the synthesized set function:
nots' :: Bool -> Values Bool
nots' x = notS x

test_nots' :: Prop
test_nots' = failing (nots' failed)

