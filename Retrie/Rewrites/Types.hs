-- Copyright (c) 2025 Andrew Farmer
-- Copyright (c) 2020-2024 Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
module Retrie.Rewrites.Types where

import Control.Monad
import Data.Maybe

import Retrie.ExactPrint
import Retrie.Expr
import Retrie.GHC
import Retrie.Quantifiers
import Retrie.Types

typeSynonymsToRewrites
  :: [(FastString, Direction)]
  -> AnnotatedModule
  -> IO (UniqFM FastString [Rewrite (LHsType GhcPs)])
typeSynonymsToRewrites specs am = fmap astA $ transformA am $ \ m -> do
  let
    fsMap = uniqBag specs
    tySyns =
      [ (rdr, (dir, (nm, hsq_explicit vars, rhs)))
        -- only hsq_explicit is available pre-renaming
      | L _ (TyClD _ (SynDecl _ nm vars _ rhs)) <- hsmodDecls $ unLoc m
      , let rdr = rdrFS (unLoc nm)
      , dir <- fromMaybe [] (lookupUFM fsMap rdr)
      ]
  fmap uniqBag $
    forM tySyns $ \(rdr, args) -> (rdr,) <$> uncurry mkTypeRewrite args

------------------------------------------------------------------------

-- | Compile a list of RULES into a list of rewrites.
mkTypeRewrite
  :: Direction
#if __GLASGOW_HASKELL__ < 908
  -> (LocatedN RdrName, [LHsTyVarBndr () GhcPs], LHsType GhcPs)
#else
  -> (LocatedN RdrName, [LHsTyVarBndr (HsBndrVis GhcPs) GhcPs], LHsType GhcPs)
#endif
  -> TransformT IO (Rewrite (LHsType GhcPs))
mkTypeRewrite d (lhsName, vars, rhs) = do
  let lhsName' = setEntryDP lhsName (SameLine 0)
  tc <- mkTyVar lhsName'
  let
    lvs = tyBindersToLocatedRdrNames vars
  args <- forM lvs $ \ lv -> do
    tv <- mkTyVar lv
    let tv' = setEntryDP tv (SameLine 1)
    return tv'
  lhsApps <- mkHsAppsTy (tc:args)
  let
    (pat, tmp) = case d of
      LeftToRight -> (lhsApps, rhs)
      RightToLeft -> (rhs, lhsApps)
  p <- pruneA pat
  t <- pruneA tmp
  return $ mkRewrite (mkQs $ map unLoc lvs) p t
