{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Lib
  ( Zipper
  , zipper
  , down
  , up
  , children
  , ichildren
  , focus
  ) where
import Control.Monad.Free
import Data.Functor.Compose
import Control.Lens hiding ((:<), children)
import Control.Comonad.Cofree
import Control.Monad
import Control.Applicative.Backwards
import Control.Comonad
import Data.Foldable
import Data.List (unfoldr)
import Control.Applicative

class (Functor f) => Idx (f :: * -> *) where
  type IxOf f :: *
  idx :: IxOf f -> Traversal' (f a) a

instance Idx [] where
  type IxOf [] = Int
  idx i = ix i

data Zipper (f :: * -> *) a = Zipper
  { parents :: [(IxOf f, Cofree f a)]
  , _focus :: Cofree f a
  } deriving Functor

focus :: Lens' (Zipper f a) a
focus f (Zipper parents foc) = Zipper parents <$> (foc & _extract %%~ f)


-- TODO: implement probper comonad instance
extract :: Zipper f a -> a
extract (Zipper _ (a:<_)) = a

-- instance Functor f => Comonad (Zipper f) where
--   extract = extract . _focus
--   duplicate :: forall f a. (Zipper f a) -> Zipper f (Zipper f a)
--   duplicate z@(Zipper parents foc) = Zipper (zipWith (\z (i,_) -> (i, z)) rezippedParents parents) (foc $> z)
--     where
--       rezippedParents :: [Zipper f a]
--       rezippedParents = unfoldr go z
--       go current =
--         let x = up current
--          in liftA2 (,) x x
--       -- go (current, []) = Nothing
--       -- go :: (Zipper f a, [(IxOf f, Cofree f a)]) -> Maybe (_, Cofree f a)
--       -- go = _



zipper :: Cofree f a -> Zipper f a
zipper f = Zipper [] f

down :: Idx f =>  IxOf f -> Zipper f a -> Maybe (Zipper f a)
down i (Zipper parents current) = Zipper ((i, current) : parents) <$> (unwrap current ^? idx i)

up :: Idx f => Zipper f a -> Maybe (Zipper f a)
up (Zipper ((i, p) : parents) current) = Just $ Zipper parents (p & _unwrap . idx i .~ current)
up _ = Nothing

rezip :: Idx f => Zipper f a -> Cofree f a
rezip z = case up z of
  Nothing -> _focus z
  Just p -> rezip p

-- | Move to a sibling
hop :: Idx f => IxOf f -> Zipper f a -> Maybe (Zipper f a)
hop i = up >=> down i

parentValues :: Traversal' (Zipper f a) a
parentValues f (Zipper parents foc) = Zipper <$> (forwards (parents & traversed . _2 . _extract %%~ Backwards . f)) <*> pure foc

children :: Traversable f => Traversal'  (Zipper f a) (Cofree f a)
children f (Zipper parents current) = Zipper parents <$> (current & _unwrap . traversed %%~ f)

ichildren :: TraversableWithIndex i f => IndexedTraversal' i (Zipper f a) (Cofree f a)
ichildren f (Zipper parents current) = Zipper parents <$> (current & _unwrap . itraversed %%@~ \i a -> indexed f i a)


roseTree :: Cofree [] Int
roseTree = 1 :< [2 :< [], 3 :< [4 :< [], 5 :< []]]
