{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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

module Zipper.Recursive.Internal where

import qualified Control.Comonad as Comonad
import Control.Comonad.Cofree
import qualified Control.Comonad.Cofree as Cofree
import qualified Control.Comonad.Trans.Cofree as CofreeF
import Control.Lens hiding (children, (:<))
import Control.Monad
import Data.Functor.Classes
import qualified Data.Functor.Foldable as FF
import Data.Maybe

-- | Alias for constraints required for many zipper operations.
type Idx i f a = (Ixed (f (Cofree f a)), IxValue (f (Cofree f a)) ~ (Cofree f a), Index (f (Cofree f a)) ~ i)

-- | The core zipper type
data Zipper i (f :: * -> *) a = Zipper
  { parents :: [(i, Cofree f a)],
    focus :: Cofree f a
  }
  deriving (Functor)

deriving instance (Eq1 f, Eq i, Eq a) => Eq (Zipper i f a)

deriving instance (Ord1 f, Ord i, Ord a) => Ord (Zipper i f a)

-- | Get the location of the current selection within its parent if we have one.
--
-- @O(1)@
currentIndex :: Zipper i f a -> Maybe i
currentIndex (Zipper ((i, _) : _) _) = Just i
currentIndex _ = Nothing

-- | Get the path to the current value from the root of the structure.
--
-- @O(depth)
currentPath :: Zipper i f a -> [i]
currentPath (Zipper parents _) = reverse $ fmap fst parents

-- | Focus the tag at the current position.
focus_ :: Lens' (Zipper i f a) a
focus_ f (Zipper parents foc) = Zipper parents <$> (foc & _extract %%~ f)

-- | Focus the currently selected sub-tree as a 'Cofree'
unwrapped_ :: Lens' (Zipper i f a) (Cofree f a)
unwrapped_ f (Zipper parents foc) = Zipper parents <$> f foc

-- TODO: implement proper comonad instance
-- extract :: Zipper i f a -> a
-- extract (Zipper _ (a :< _)) = a

-- instance Functor f => Comonad (Zipper i f) where
--   extract = extract . _focus
--   duplicate :: forall f a. (Zipper i f a) -> Zipper i f (Zipper i f a)
--   duplicate z@(Zipper parents foc) = Zipper (zipWith (\z (i,_) -> (i, z)) rezippedParents parents) (foc $> z)
--     where
--       rezippedParents :: [Zipper i f a]
--       rezippedParents = unfoldr go z
--       go current =
--         let x = up current
--          in liftA2 (,) x x
--       -- go (current, []) = Nothing
--       -- go :: (Zipper i f a, [(i, Cofree f a)]) -> Maybe (_, Cofree f a)
--       -- go = _

-- | A useful combinator for chaining operations which might fail.
-- If an operation fails, the original zipper is returned.
--
-- E.g.
--
-- >>> tug up z
tug :: (a -> Maybe a) -> a -> a
tug f a = fromMaybe a (f a)

-- | Create a zipper over a cofree structure
zipper :: Cofree f a -> Zipper i f a
zipper f = Zipper [] f

-- | Create a zipper from a recursive type, tagging it with '()'
fromRecursive :: FF.Recursive t => t -> Zipper i (FF.Base t) ()
fromRecursive t = zipper $ Cofree.unfold (((),) . FF.project) t

-- | Create a zipper from a recursive type, given a function to generate annotations.
tagged :: FF.Recursive t => (t -> a) -> t -> Zipper i (FF.Base t) a
tagged f t = zipper $ Cofree.unfold (\x -> (f x, FF.project x)) t

-- | Select the subtree at the given location.
--
-- @O(1)@
down :: (Idx i f a) => i -> Zipper i f a -> Maybe (Zipper i f a)
down i (Zipper parents current) = Zipper ((i, current) : parents) <$> (current ^? _unwrap . ix i)

-- | Select the parent of the current location.
--
-- @O(1)@
up :: Idx i f a => Zipper i f a -> Maybe (Zipper i f a)
up (Zipper ((i, p) : parents) current) = Just $ Zipper parents (p & _unwrap . ix i .~ current)
up _ = Nothing

-- | Re-zip the entire tree.
--
-- @O(d)@
rezip :: Idx i f a => Zipper i f a -> Cofree f a
rezip z = case up z of
  Nothing -> focus z
  Just p -> rezip p

-- | Rezip, forget all tags, and flatten the structure.
--
-- @O(d)@
flatten :: (FF.Corecursive f, Idx i (FF.Base f) a) => Zipper i (FF.Base f) a -> f
flatten = FF.cata alg . rezip
  where
    alg (_ CofreeF.:< fv) = FF.embed fv

-- | Move to the sibling which is located at 'i' in its parent.
--
-- @O(1)@
--
-- @
-- sibling i = up >=> down i
-- @
sibling :: Idx i f a => i -> Zipper i f a -> Maybe (Zipper i f a)
sibling i = up >=> down i

-- parentTags :: Traversal' (Zipper i f a) a
-- parentTags f (Zipper parents foc) = Zipper <$> (forwards (parents & traversed . _2 . _extract %%~ Backwards . f)) <*> pure foc

-- | Traversal over all subtrees of the current location.
children_ :: Traversable f => Traversal' (Zipper i f a) (Cofree f a)
children_ f (Zipper parents current) = Zipper parents <$> (current & _unwrap . traversed %%~ f)

-- | Indexed traversal over all subtrees of the current location.
ichildren_ :: TraversableWithIndex i f => IndexedTraversal' i (Zipper i f a) (Cofree f a)
ichildren_ f (Zipper parents current) = Zipper parents <$> (current & _unwrap . itraversed %%@~ \i a -> indexed f i a)

-- | Get the base-functor at the current location.
--
-- @O(1)@
branches :: Zipper i f a -> f (Cofree f a)
branches (Zipper _ (_ :< cs)) = cs

-- | A lens over the base-functor at the current location.
branches_ :: Lens' (Zipper i f a) (f (Cofree f a))
branches_ = lens getter setter
  where
    getter (Zipper _ (_ :< f)) = f
    setter (Zipper p (a :< _)) f = (Zipper p (a :< f))

-- retag :: Functor f => (a -> f b -> b) -> Cofree f a -> Cofree f b
-- retag f (a :< fr) =
--   let cs = fmap (retag f) fr
--    in (f a $ fmap Comonad.extract cs) :< cs

-- | Fold a zipper from bottom to top.
--
-- @O(n)@
fold :: (Functor f, Idx i f a) => (a -> f r -> r) -> Zipper i f a -> r
fold f = FF.cata (\(a CofreeF.:< fr) -> f a fr) . rezip
