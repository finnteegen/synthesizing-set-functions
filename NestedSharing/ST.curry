{-# OPTIONS_FRONTEND -W no-incomplete-patterns #-}

--- This module defines the structure and some generic operations
--- for search trees.

module ST where

import Findall (allValues)

--------------------------------------------------------------------------------

--- Does the HNF computation of the argument fail?
isFail :: a -> Bool
isFail x = null (allValues (x `seq` ()))

--------------------------------------------------------------------------------

--- Type to represent choice identifiers.
type ID = Int

type IDSupply = Int

initSupply :: IDSupply
initSupply = 1

uniqueID :: IDSupply -> ID
uniqueID i = i

leftSupply :: IDSupply -> IDSupply
leftSupply i = 2 * i

rightSupply :: IDSupply -> IDSupply
rightSupply i = 2 * i + 1

--------------------------------------------------------------------------------

--- Type to represent choice decisions.
data Decision = Left | Right

--------------------------------------------------------------------------------

--- Data type to represent search trees where failures can be
--- inside or outside.
--- Note that the actual values are head normal forms.
--- The evaluation to normal form will be done when a set functions
--- returns a value set.
data ST a = Val a                       -- a value (in head normal form)
          | Uneval a                    -- an unevaluated value from outside
          | Fail Int                    -- failure with level
          | Choice Int ID (ST a) (ST a) -- non-deterministic choice with
                                        -- identifier and level

--- Generic operation to apply a non-deterministic operation defined
--- on a single head normal form to a search tree.
applyST :: (a -> ST b) -> ST a -> ST b
applyST f (Val x)            = f x
applyST f (Uneval x)         = if isFail x then Fail 0 else f x
applyST _ (Fail l)           = Fail l
applyST f (Choice l i s1 s2) = Choice l i (f `applyST` s1) (f `applyST` s2)

--------------------------------------------------------------------------------

--- A type with the `NF` property must provide a method `nf`
--- to evaluate an expression in head normal form into a search tree
--- where all `Val` arguments are fully evaluated, i.e., do not
--- contain choices or failures in subterms.
class NF a where
  nf :: a -> ST a

-- This operation extends the operation `nf` on search trees.
nfST :: NF a => ST a -> ST a
nfST (Val x)            = nf x
nfST (Uneval x)         = if isFail x then Fail 0 else x `seq` nf x
nfST (Fail l)           = Fail l
nfST (Choice l i s1 s2) = Choice l i (nfST s1) (nfST s2)

-- Some `NF` instances for base types.
instance NF Int where
  nf x = Val x

instance NF Bool where
  nf x = Val x

instance NF Char where
  nf x = Val x
--------------------------------------------------------------------------------

--- The head normal form of a list structure with non-deterministic components.
data STList a = Nil | Cons (ST a) (ST (STList a))

instance NF a => NF (STList a) where
  nf Nil           = Val Nil
  nf (Cons sx sxs) = case nfST sx of
    Choice l i s1 s2 -> Choice l i (nfST (Val (Cons s1 sxs)))
                                   (nfST (Val (Cons s2 sxs)))
    Fail l           -> Fail l
    sy               -> case nfST sxs of
      Choice l i s1 s2 -> Choice l i (nfST (Val (Cons sy s1)))
                                     (nfST (Val (Cons sy s2)))
      Fail l           -> Fail l
      sys              -> Val (Cons sy sys)

--------------------------------------------------------------------------------

--- The head normal form of a pair structure with non-deterministic components.
data STPair a b = Pair (ST a) (ST b)

instance (NF a, NF b) => NF (STPair a b) where
  nf (Pair x1 x2) = case nfST x1 of
    Choice n i c1 c2 -> Choice n i (nfST (Val (Pair c1 x2)))
                                   (nfST (Val (Pair c2 x2)))
    Fail n -> Fail n
    y1 -> case nfST x2 of
           Choice n i c1 c2 -> Choice n i (nfST (Val (Pair y1 c1)))
                                          (nfST (Val (Pair y1 c2)))
           Fail n           -> Fail n
           y2               -> Val (Pair y1 y2)

--------------------------------------------------------------------------------

--- Computes the list of all values (normal forms) represented in a search tree.
stValues :: NF a => ST a -> [a]
stValues = searchDFS . nfST

--- Searches all values in a search tree by a depth-first search strategy.
--- Outside failures lead to a failure only if there is no other value.
searchDFS :: ST a -> [a]
searchDFS st = maybe failed id (searchDFS' [] st)
 where
  searchDFS' _ (Val x)            = Just [x]
  searchDFS' _ (Fail l)           = if l == 0 then Nothing else Just []
  searchDFS' m (Choice _ i s1 s2) =
    case lookup i m of
      Nothing    -> concVals (searchDFS' ((i,Left):m) s1)
                             (searchDFS' ((i,Right):m) s2)
      Just Left  -> searchDFS' m s1
      Just Right -> searchDFS' m s2

  concVals Nothing   ys = ys
  concVals (Just xs) ys = Just (xs ++ maybe [] id ys)

--- Computes the non-deterministic list of all values (normal forms)
--- represented in a search tree.
stValuesP :: NF a => Int -> ST a -> ST (STList a)
stValuesP n = searchDFSP n [] . nfST

-- Computes the list of all normal forms of a search tree value.
-- The first argument is the encapsulation level so that
-- failures and non-determinism outside this level are not encapsulated.
searchDFSP :: NF a => Int -> [(ID,Decision)] -> ST a -> ST (STList a)
searchDFSP _ _ (Val x)            = Val (Cons (Val x) (Val Nil))
searchDFSP l _ (Fail n)           = if n == l then Val Nil else Fail n
searchDFSP l m (Choice n i s1 s2) =
  if n == l then case lookup i m of
                   Nothing    -> concValsP (searchDFSP l ((i,Left):m) s1)
                                           (searchDFSP l ((i,Right):m) s2)
                   Just Left  -> searchDFSP l m s1
                   Just Right -> searchDFSP l m s2
            else Choice n i (searchDFSP l m s1) (searchDFSP l m s2)

concValsP :: ST (STList a) -> ST (STList a) -> ST (STList a)
concValsP (Val Nil)           sys                = sys
concValsP (Val (Cons sx sxs)) sys                =
  Val (Cons sx (concValsP sxs (getValuesP sys)))
concValsP (Choice n i s1 s2)  sys                =
  Choice n i (concValsP s1 sys) (concValsP s2 sys)
concValsP (Fail _)            sy@(Val _)         = sy
concValsP (Fail n)            (Fail m)           = Fail (max n m)
concValsP (Fail n)            (Choice m i s1 s2) =
  Choice m i (concValsP (Fail n) s1) (concValsP (Fail n) s2)

-- Removes failures from a list.
getValuesP :: ST (STList a) -> ST (STList a)
getValuesP (Val x)            = Val x
getValuesP (Fail _)           = Val Nil
getValuesP (Choice l i s1 s2) = Choice l i (getValuesP s1) (getValuesP s2)

--------------------------------------------------------------------------------

-- The following multiparameter type class is what we would wish for in
-- order to realize an elegant automatic transformation of programs.
-- 
-- class ConvertST a b where
--   toValST :: a -> b
--   fromValST :: b -> a
--
-- The method `toValST` converts a Curry value to its ST representation.
-- 'fromValST` converts a value in ST representation back to
-- its corresponding Curry value. When converting a Curry value to its
-- ST representation, we wrap constructor arguments in an `Uneval`
-- constructor, which is done by using the `toST` function introduced
-- later. This way we can ensure that we do not evaluate Curry expressions
-- that are not demanded.
-- We would have to provide instances of the multiparameter type class for
-- each data type and its translation, e.g., the following instances.
--
-- instance ConvertST Int Int
-- instance ConvertST a b => ConvertST [a] (STList b)
--
-- However, since Curry currently does not support multiparameter type
-- classes we have to provide specialized implementations of its methods.
--
-- In the following we provide these specialized implementations for the
-- aforementioned instances.

toValST_Int_Int :: Int -> Int
toValST_Int_Int = id

fromValST_Int_Int :: Int -> Int
fromValST_Int_Int = id

toValST_Bool_Bool :: Bool -> Bool
toValST_Bool_Bool = id

fromValST_Bool_Bool :: Bool -> Bool
fromValST_Bool_Bool = id

toValST_List_STList :: (a -> ST b) -> [a] -> STList b
toValST_List_STList _        []     = Nil
toValST_List_STList toST_a_b (x:xs) =
  Cons (toST_a_b x) (toST_List_STList toST_a_b xs)

toValST_Pair_STPair :: (a -> ST c) -> (b -> ST d) -> (a,b) -> STPair c d
toValST_Pair_STPair toST_a_c toST_b_d (x,y) = Pair (toST_a_c x) (toST_b_d y)

fromValST_List_STList :: (a -> b) -> STList a -> [b]
fromValST_List_STList _              Nil                     = []
fromValST_List_STList fromValST_b_a (Cons (Val x) (Val xs)) =
  fromValST_b_a x : fromValST_List_STList fromValST_b_a xs

fromValST_Pair_STPair :: (a -> b) -> (c -> d) -> STPair a c -> (b,d)
fromValST_Pair_STPair fromValST_b_a fromValST_d_c (Pair (Val x) (Val y)) =
  (fromValST_b_a x, fromValST_d_c y)

--------------------------------------------------------------------------------

-- We further need a function that returns a search tree representation of
-- a Curry value by wrapping the value translated into its ST representation
-- in an `Uneval` constructor. Aside from the use in `toValST` we will need
-- this functionality when calling a set function where we wrap every arguments
-- this way.
--
-- toST :: ConvertST a b => a -> ST b
-- toST = Uneval . toValST
--
-- Because we do not have the multiparameter type class `ConvertST` available
-- in Curry, we have to provide specialized implementations of this
-- overloaded function.

toST_Int_Int :: Int -> ST Int
toST_Int_Int = Uneval . toValST_Int_Int

toST_Bool_Bool :: Bool -> ST Bool
toST_Bool_Bool = Uneval . toValST_Bool_Bool

toST_List_STList :: (a -> ST b) -> [a] -> ST (STList b)
toST_List_STList toST_a_b = Uneval . toValST_List_STList toST_a_b

toST_Pair_STPair :: (a -> ST b) -> (c -> ST d) -> (a,c) -> ST (STPair b d)
toST_Pair_STPair toST_a_b toST_c_d =
  Uneval . toValST_Pair_STPair toST_a_b toST_c_d

--------------------------------------------------------------------------------

-- For simplicity, we represent multisets of values as lists.
type Values a = [a]

-- Also, we need a function that translates a search tree representation
-- to the multiset of its Curry values.
--
-- fromST :: (ConvertST a b, NF b) => ST b -> Values a
-- fromST = map fromValST . stValues

-- Like before, we have to provide specialized implementations of this
-- overloaded function.

fromST_Int_Int :: ST Int -> Values Int
fromST_Int_Int = map fromValST_Int_Int . stValues

fromST_Bool_Bool :: ST Bool -> Values Bool
fromST_Bool_Bool = map fromValST_Bool_Bool . stValues

fromST_List_STList :: NF a => (a -> b) -> ST (STList a) ->  Values [b]
fromST_List_STList fromValST_b_a =
  map (fromValST_List_STList fromValST_b_a) . stValues

fromST_Pair_STPair :: (NF a, NF c) => (a -> b) -> (c -> d) -> ST (STPair a c)
                   ->  Values (b,d)
fromST_Pair_STPair fromValST_b_a fromValST_d_c =
  map (fromValST_Pair_STPair fromValST_b_a fromValST_d_c) . stValues

--------------------------------------------------------------------------------

-- Sometimes it is helpful to lift functions on base types
-- to plural functions. Note that these operations are only
-- applicable to strict and knowingly determinstic functions
-- that don't produce failures.
-- For this reason, we omit the additional `IDSupply` and
-- encapsulation level parameters in their lifted form.

--- Lifts a unary function into a plural function.
lift1P :: (a -> b) -> ST a -> ST b
lift1P f sx = (Val . f) `applyST` sx

--- Lifts a binary function into a plural function.
lift2P :: (a -> b -> c) -> ST a -> ST b -> ST c
lift2P f sx sy = lift2X `applyST` sx
 where lift2X x = lift2XY `applyST` sy
        where lift2XY y = Val (f x y)

--- Lifts a ternary function into a plural function.
lift3P :: (a -> b -> c -> d) -> ST a -> ST b -> ST c -> ST d
lift3P f sx sy sz = lift3X `applyST` sx
 where lift3X x = lift3XY `applyST` sy
        where lift3XY y = lift3XYZ `applyST` sz
               where lift3XYZ z = Val (f x y z)

