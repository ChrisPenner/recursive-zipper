{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Zipper
  ( Zipper,
    zipper,
    down,
    up,
    rezip,
    flatten,
    Zipper.fold,
    sibling,
    children,
    ichildren,
    focus,
    focus_,
    unwrapped_,
    tagged,
    fromRecursive,
    Idx (..),
    tug,
    foldSpine,
    retag,
    branches,
    branches_,
    currentIndex,
  )
where

import Control.Applicative.Backwards
import qualified Control.Comonad as Comonad
import Control.Comonad.Cofree
import qualified Control.Comonad.Cofree as Cofree
import qualified Control.Comonad.Trans.Cofree as CofreeF
import Control.Lens hiding (children, (:<))
import Control.Monad
import Data.Functor.Classes
import qualified Data.Functor.Foldable as FF
import Data.Maybe

class (TraversableWithIndex (IxOf f) f) => Idx (f :: * -> *) where
  type IxOf f :: *
  idx :: IxOf f -> Traversal' (f a) a

instance Idx [] where
  type IxOf [] = Int
  idx = ix

data Zipper (f :: * -> *) a = Zipper
  { parents :: [(IxOf f, Cofree f a)],
    focus :: Cofree f a
  }
  deriving (Functor)

-- deriving instance (Eq1 f, Eq (IxOf f), Eq a) => Eq (Zipper f a)
deriving instance (Eq1 f, Eq (IxOf f), Eq a) => Eq (Zipper f a)

deriving instance (Ord1 f, Ord (IxOf f), Ord a) => Ord (Zipper f a)

currentIndex :: Zipper f a -> Maybe (IxOf f)
currentIndex (Zipper ((i, _) : _) _) = Just i
currentIndex _ = Nothing

focus_ :: Lens' (Zipper f a) a
focus_ f (Zipper parents foc) = Zipper parents <$> (foc & _extract %%~ f)

unwrapped_ :: Lens' (Zipper f a) (Cofree f a)
unwrapped_ f (Zipper parents foc) = Zipper parents <$> f foc

-- TODO: implement proper comonad instance
extract :: Zipper f a -> a
extract (Zipper _ (a :< _)) = a

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

tug :: (a -> Maybe a) -> a -> a
tug f a = fromMaybe a (f a)

zipper :: Cofree f a -> Zipper f a
zipper f = Zipper [] f

fromRecursive :: FF.Recursive t => t -> Zipper (FF.Base t) ()
fromRecursive t = zipper $ Cofree.unfold (((),) . FF.project) t

tagged :: FF.Recursive t => (t -> a) -> t -> Zipper (FF.Base t) a
tagged f t = zipper $ Cofree.unfold (\x -> (f x, FF.project x)) t

down :: Idx f => IxOf f -> Zipper f a -> Maybe (Zipper f a)
down i (Zipper parents current) = Zipper ((i, current) : parents) <$> (unwrap current ^? idx i)

up :: Idx f => Zipper f a -> Maybe (Zipper f a)
up (Zipper ((i, p) : parents) current) = Just $ Zipper parents (p & _unwrap . idx i .~ current)
up _ = Nothing

rezip :: Idx f => Zipper f a -> Cofree f a
rezip z = case up z of
  Nothing -> focus z
  Just p -> rezip p

flatten :: (FF.Corecursive f, Idx (FF.Base f)) => Zipper (FF.Base f) a -> f
flatten = FF.cata alg . rezip
  where
    alg (_ CofreeF.:< fv) = FF.embed fv

-- | Move to a sibling
sibling :: Idx f => IxOf f -> Zipper f a -> Maybe (Zipper f a)
sibling i = up >=> down i

parentValues :: Traversal' (Zipper f a) a
parentValues f (Zipper parents foc) = Zipper <$> (forwards (parents & traversed . _2 . _extract %%~ Backwards . f)) <*> pure foc

children :: Traversable f => Traversal' (Zipper f a) (Cofree f a)
children f (Zipper parents current) = Zipper parents <$> (current & _unwrap . traversed %%~ f)

branches :: Zipper f a -> f (Cofree f a)
branches (Zipper _ (_ :< cs)) = cs

branches_ :: Lens' (Zipper f a) (f (Cofree f a))
branches_ = lens getter setter
  where
    getter (Zipper _ (_ :< f)) = f
    setter (Zipper p (a :< _)) f = (Zipper p (a :< f))

ichildren :: TraversableWithIndex i f => IndexedTraversal' i (Zipper f a) (Cofree f a)
ichildren f (Zipper parents current) = Zipper parents <$> (current & _unwrap . itraversed %%@~ \i a -> indexed f i a)

roseTree :: Cofree [] Int
roseTree = 1 :< [2 :< [], 3 :< [4 :< [], 5 :< []]]

-- Recomputes the spine at the current position, then at every position from that point
-- upwards until the zipper is closed, returning the result.
foldSpine :: (Functor f, Idx f) => (a -> f a -> a) -> Zipper f a -> a
foldSpine f z =
  case up z of
    Nothing -> Zipper.extract z
    Just (Zipper parents (a :< cs)) ->
      let next = f a (fmap Comonad.extract cs)
       in foldSpine f (Zipper parents (next :< cs))

retag :: Functor f => (a -> f b -> b) -> Cofree f a -> Cofree f b
retag f (a :< fr) =
  let cs = fmap (retag f) fr
   in (f a $ fmap Comonad.extract cs) :< cs

-- foldZipper :: forall f a r. Functor f => (a -> f r -> r) -> Zipper f a -> r
-- foldZipper f (Zipper parents foc) =
--   FF.cata alg foc
--   where
--     alg :: CofreeF.CofreeF f a r -> r
--     alg (a CofreeF.:< fr) = f a fr

fold :: (Idx f, Functor f) => (a -> f r -> r) -> Zipper f a -> r
fold f = FF.cata (\(a CofreeF.:< fr) -> f a fr) . rezip
