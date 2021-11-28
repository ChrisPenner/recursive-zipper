module Zipper.Recursive
  ( -- * Core type
    Z.Zipper,
    Z.Idx,

    -- * Constructing Zippers
    Z.zipper,
    Z.fromRecursive,
    Z.tagged,

    -- * Movement
    Z.down,
    Z.up,
    Z.sibling,
    Z.tug,

    -- * Folding and flattening
    Z.rezip,
    Z.flatten,
    Z.fold,

    -- * Getters
    Z.focus,
    Z.branches,
    Z.currentIndex,

    -- * Optics
    Z.focus_,
    Z.unwrapped_,
    Z.branches_,
    Z.children_,
    Z.ichildren_,
  )
  where

import Zipper.Recursive.Internal as Z
