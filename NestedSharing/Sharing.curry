module Sharing where

-- An example for nested set functions inspired by Michael Hanus' lecture
-- 'Deklarative Programmiersprachen' (declarative programming languages).

import qualified SetFunctions as SF
import Test.Prop
import ST

--------------------------------------------------------------------------------

fun :: [Int]
fun = let coin = 0 ? 1 in [coin, coin]

fun2 :: Int -> [Int]
fun2 x = let coin = x ? 2 in [coin, coin]

dup :: Int -> [Int]
dup x = [x,x]

double :: Int -> Int
double x = x + x

double01 :: Int
double01 = double (0?1)

main1, main2 :: SF.Values [Int]
main1 = SF.set0 fun
main2 = SF.set1 fun2 (0?1)
main3 :: SF.Values Int
main3 = SF.set0 double01

--------------------------------------------------------------------------------

funP :: IDSupply -> Int -> ST (STList Int)
funP s l = let coin = Choice l (uniqueID s) (Val 0) (Val 1)
           in Val (Cons coin (Val (Cons coin (Val Nil))))

funS :: Values [Int]
funS = fromST_List_STList fromValST_Int_Int (funP initSupply 1)

fun2P :: IDSupply -> Int -> ST Int -> ST (STList Int)
fun2P s l x = let coin = Choice l (uniqueID s) x (Val 2)
              in Val (Cons coin (Val (Cons coin (Val Nil))))

fun2S :: Int -> Values [Int]
fun2S x =
  fromST_List_STList fromValST_Int_Int (fun2P initSupply 1 (toST_Int_Int x))

dupP :: IDSupply -> Int -> ST Int -> ST (STList Int)
dupP _ _ x = Val (Cons x (Val (Cons x (Val Nil))))

dupS :: Int -> Values [Int]
dupS x =
  fromST_List_STList fromValST_Int_Int (dupP initSupply 1 (toST_Int_Int x))

plusP :: ST Int -> ST Int -> ST Int
plusP = lift2P (+)

doubleP :: IDSupply -> Int -> ST Int -> ST Int
doubleP _ _ x = plusP x x

doubleS :: Int -> Values Int
doubleS x = fromST_Int_Int (doubleP initSupply 1 (toST_Int_Int x))

double01P :: IDSupply -> Int -> ST Int
double01P s l = doubleP (leftSupply s) l (Choice l (uniqueID s) (Val 0) (Val 1))

double01S :: Values Int
double01S = fromST_Int_Int (double01P initSupply 1)

--------------------------------------------------------------------------------

-- Tests:
propS1, propS2, propS3, propS4, propS5 :: Prop
propS1 = funS -=- [[0,0],[1,1]]
propS2 = fun2S (0?1) <~> ([[0,0],[2,2]] ? [[1,1],[2,2]])
propS3 = dupS (0?1) <~> ([[0,0]] ? [[1,1]])
propS4 = doubleS (0?1) <~> ([0] ? [2])
propS5 = double01S -=- [0,2]

