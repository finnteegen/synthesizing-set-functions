module Sharing where

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

funP :: IDSupply -> ST (STList Int)
funP s = let coin = Choice (uniqueID s) (Val 0) (Val 1)
         in Val (Cons coin (Val (Cons coin (Val Nil))))

funS :: Values [Int]
funS = fromST_List_STList fromValST_Int_Int (funP initSupply)

fun2P :: IDSupply -> ST Int -> ST (STList Int)
fun2P s x = let coin = Choice (uniqueID s) x (Val 2)
            in Val (Cons coin (Val (Cons coin (Val Nil))))

fun2S :: Int -> Values [Int]
fun2S x =
  fromST_List_STList fromValST_Int_Int (fun2P initSupply (toST_Int_Int x))

dupP :: IDSupply -> ST Int -> ST (STList Int)
dupP _ x = Val (Cons x (Val (Cons x (Val Nil))))

dupS :: Int -> Values [Int]
dupS x = fromST_List_STList fromValST_Int_Int (dupP initSupply (toST_Int_Int x))

plusP :: ST Int -> ST Int -> ST Int
plusP = lift2P (+)

doubleP :: IDSupply -> ST Int -> ST Int
doubleP _ x = plusP x x

doubleS :: Int -> Values Int
doubleS x = fromST_Int_Int (doubleP initSupply (toST_Int_Int x))

double01P :: IDSupply -> ST Int
double01P s = doubleP (leftSupply s) (Choice (uniqueID s) (Val 0) (Val 1))

double01S :: Values Int
double01S = fromST_Int_Int (double01P initSupply)

--------------------------------------------------------------------------------

-- Tests:
propS1, propS2, propS3, propS4, propS5 :: Prop
propS1 = funS -=- [[0,0],[1,1]]
propS2 = fun2S (0?1) <~> ([[0,0],[2,2]] ? [[1,1],[2,2]])
propS3 = dupS (0?1) <~> ([[0,0]] ? [[1,1]])
propS4 = doubleS (0?1) <~> ([0] ? [2])
propS5 = double01S -=- [0,2]

