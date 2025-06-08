-- Copyright (c) 2025 Andrew Farmer
-- Copyright (c) 2020-2024 Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE RecordWildCards #-}
module Retrie.Rewrites.Rules (rulesToRewrites) where

import Data.Generics
import Data.Maybe

import Retrie.ExactPrint
import Retrie.GHC
import Retrie.Quantifiers
import Retrie.Types

rulesToRewrites
  :: [(FastString, Direction)]
  -> AnnotatedModule
  -> IO (UniqFM RuleName [Rewrite (LHsExpr GhcPs)])
rulesToRewrites specs am = fmap astA $ transformA am $ \ m -> do
  let
    fsMap = uniqBag specs

  uniqBag <$> sequence
    [ mkRuleRewrite dir info
    | info@RuleInfo{..} <- everything (++) (mkQ [] ruleInfo) m
    , dir <- fromMaybe [] (lookupUFM fsMap riName)
    ]

------------------------------------------------------------------------

mkRuleRewrite
  :: Direction
  -> RuleInfo
  -> TransformT IO (RuleName, Rewrite (LHsExpr GhcPs))
mkRuleRewrite RightToLeft (RuleInfo name qs lhs rhs) =
  mkRuleRewrite LeftToRight (RuleInfo name qs rhs lhs)
mkRuleRewrite _ RuleInfo{..} = do
  p <- pruneA (setEntryDP riLHS (SameLine 1))
  t <- pruneA (setEntryDP riRHS (SameLine 1))
  -- lift $ debugPrint Loud "mkRuleRewrite" [showAstA p, showAstA t]
  return (riName, mkRewrite (mkQs riQuantifiers) p t)
