-- Copyright (c) 2025 Andrew Farmer
-- Copyright (c) 2020-2024 Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Retrie.Context
  ( ContextUpdater
  , updateContext
  , emptyContext
  ) where

import Control.Monad.IO.Class
import Data.Char (isDigit)
import Data.Either (partitionEithers)
import Data.Generics hiding (Fixity)
import Data.List
import Data.Maybe

import Retrie.AlphaEnv
import Retrie.ExactPrint
import Retrie.Fixity
import Retrie.FreeVars
import Retrie.GHC
import Retrie.Substitution
import Retrie.SYB
import Retrie.Types
import Retrie.Universe

-------------------------------------------------------------------------------

-- | Type of context update functions for 'apply'.
-- When defining your own 'ContextUpdater', you probably want to extend
-- 'updateContext' using SYB combinators such as 'mkQ' and 'extQ'.
type ContextUpdater = forall m. MonadIO m => GenericCU (TransformT m) Context

-- | Default context update function.
updateContext :: forall m. MonadIO m => GenericCU (TransformT m) Context
updateContext c i =
  const (return c)
    `extQ` (return . updExp)
    `extQ` (return . updType)
    `extQ` (return . updMatch)
    `extQ` (return . updGRHSs)
    `extQ` (return . updGRHS)
    `extQ` (return . updStmt)
    `extQ` (return . updPat)
    `extQ` updStmtList
    `extQ` (return . updHsBind)
    `extQ` (return . updTyClDecl)
  where
    neverParen = c { ctxtParentPrec = NeverParen }

    updExp :: HsExpr GhcPs -> Context
    updExp HsApp{} = withPrec c (SourceText "HsApp") 10 InfixL i
    updExp (OpApp _ _ op _)
      | Fixity source prec dir <- lookupOp op $ ctxtFixityEnv c =
          withPrec c source prec dir i
    updExp (HsLet _ _ lbs _ _) = addInScope neverParen $ collectLocalBinders CollNoDictBinders lbs
    updExp _ = neverParen

    updType :: HsType GhcPs -> Context
    updType HsAppTy{} = withPrec c (SourceText "HsAppTy") (getPrec appPrec) InfixL i
    updType HsFunTy{} = withPrec c (SourceText "HsFunTy") (getPrec funPrec) InfixR (i - 1)
    updType _ = withPrec c (SourceText "HsType") (getPrec appPrec) InfixN i

    updMatch :: Match GhcPs (LHsExpr GhcPs) -> Context
    updMatch
      | i == 2  -- m_pats field
      = addInScope c{ctxtParentPrec = IsLhs} . collectPatsBinders CollNoDictBinders . m_pats
      | otherwise = addInScope neverParen . collectPatsBinders CollNoDictBinders . m_pats
      where

    updGRHSs :: GRHSs GhcPs (LHsExpr GhcPs) -> Context
    updGRHSs = addInScope neverParen . collectLocalBinders CollNoDictBinders . grhssLocalBinds

    updGRHS :: GRHS GhcPs (LHsExpr GhcPs) -> Context
    updGRHS (GRHS _ gs _)
        -- binders are in scope over the body (right child) only
      | i > firstChild = addInScope neverParen bs
      | otherwise = fst $ updateSubstitution neverParen bs
      where
        bs = collectLStmtsBinders CollNoDictBinders gs

    updStmt :: Stmt GhcPs (LHsExpr GhcPs) -> Context
    updStmt _ = neverParen

    updStmtList :: [LStmt GhcPs (LHsExpr GhcPs)] -> TransformT m Context
    updStmtList [] = return neverParen
    updStmtList (ls:_)
        -- binders are in scope over tail of list (right child)
      | i > 0 = insertDependentRewrites neverParen bs ls
        -- lets are recursive in do-blocks
      | L _ (LetStmt _ bnds) <- ls =
          return $ addInScope neverParen $ collectLocalBinders CollNoDictBinders bnds
      | otherwise = return $ fst $ updateSubstitution neverParen bs
      where
        bs = collectLStmtBinders CollNoDictBinders ls

    updHsBind :: HsBind GhcPs -> Context
    updHsBind FunBind{..} =
      let rdr = unLoc fun_id
      in addBinders (addInScope neverParen [rdr]) [rdr]
    updHsBind _ = neverParen

    updTyClDecl :: TyClDecl GhcPs -> Context
    updTyClDecl SynDecl{..} = addInScope neverParen [unLoc tcdLName]
    updTyClDecl DataDecl{..} = addInScope neverParen [unLoc tcdLName]
    updTyClDecl ClassDecl{..} = addInScope neverParen [unLoc tcdLName]
    updTyClDecl _ = neverParen

    updPat :: Pat GhcPs -> Context
    updPat _ = neverParen

getPrec :: PprPrec -> Int
getPrec (PprPrec prec) = prec

withPrec :: Context -> SourceText -> Int -> FixityDirection -> Int -> Context
withPrec c source prec dir i = c{ ctxtParentPrec = HasPrec fixity }
  where
    fixity = Fixity source prec d
    d = case dir of
      InfixL
        | i == firstChild -> InfixL
        | otherwise -> InfixN
      InfixR
        | i == firstChild -> InfixN
        | otherwise -> InfixR
      InfixN -> InfixN

-- | Create an empty 'Context' with given 'FixityEnv', rewriter, and dependent
-- rewrite generator.
emptyContext :: FixityEnv -> Rewriter -> Rewriter -> Context
emptyContext ctxtFixityEnv ctxtRewriter ctxtDependents = Context{..}
  where
    ctxtBinders = []
    ctxtInScope = emptyAlphaEnv
    ctxtParentPrec = NeverParen
    ctxtSubst = Nothing

-- Deal with Trees-That-Grow adding extension points
-- as the first child everywhere.
firstChild :: Int
firstChild = 1

-- | Add dependent rewrites to 'ctxtRewriter' if necessary.
insertDependentRewrites
  :: (Matchable k, MonadIO m) => Context -> [RdrName] -> k -> TransformT m Context
insertDependentRewrites c bs x = do
  r <- runRewriter id c (ctxtDependents c) x
  let
    c' = addInScope c bs
  case r of
    NoMatch -> return c'
    MatchResult _ Template{..} -> do
      let
        rrs = fromMaybe [] tDependents
        ds = rewritesWithDependents rrs
        f = foldMap (mkLocalRewriter $ ctxtInScope c')
      return c'
        { ctxtRewriter = f rrs <> ctxtRewriter c'
        , ctxtDependents = f ds <> ctxtDependents c'
        }

-- | Add set of binders to 'ctxtInScope'.
addInScope :: Context -> [RdrName] -> Context
addInScope c bs =
  c' { ctxtInScope = foldr extendAlphaEnv (ctxtInScope c') bs' }
  where
    (c', bs') = updateSubstitution c bs

-- | Add set of binders to 'ctxtBinders'.
addBinders :: Context -> [RdrName] -> Context
addBinders c bs = c { ctxtBinders = bs ++ ctxtBinders c }

-- Capture-avoiding substitution
--------------------------------------------------------------------------------

-- | Update the Context's substitution appropriately for a set of binders.
-- Returns a new Context and a potentially alpha-renamed set of binders.
updateSubstitution :: Context -> [RdrName] -> (Context, [RdrName])
updateSubstitution c rdrs =
  case ctxtSubst c of
    Nothing -> (c, rdrs)
    Just sub ->
      let
        -- This prevents substituting for 'x' under a binding for 'x'.
        sub' = deleteSubst sub $ map rdrFS rdrs
        -- Compute free vars of substitution that could possibly be captured.
        fvs = substFVs sub'
        -- Partition binders into noncapturing and capturing.
        (noncapturing, capturing) =
          partitionEithers $ map (updateBinder fvs) rdrs
        -- Extend substitution with alpha-renamings.
        alphaSub = foldl' (uncurry . extendSubst) sub'
          [ (rdrFS rdr, HoleRdr rdr') | (rdr, rdr') <- capturing ]
        -- There are no telescopes in source Haskell, so order doesn't matter.
        -- Capturing should be rare, so put it first to avoid quadratic append.
        rdrs' = map snd capturing ++ noncapturing
      in (c { ctxtSubst = Just alphaSub }, rdrs')

-- | Check if RdrName is in FreeVars.
--
-- If so, return a pair of it and its new name (Right).
-- If not, return it unchanged (Left).
updateBinder :: FreeVars -> RdrName -> Either RdrName (RdrName, RdrName)
updateBinder fvs rdr
  | elemFVs rdr fvs = Right (rdr, renameBinder rdr fvs)
  | otherwise = Left rdr

-- | Given a RdrName, rename it to something not in given FreeVars.
--
--   x => x1
--   x1 => x2
--   x9 => x10
--
-- etc.
--
-- Only works on unqualified RdrNames. This is fine, as we only use this to
-- rename local binders.
renameBinder :: RdrName -> FreeVars -> RdrName
renameBinder rdr fvs = headNoWarn
  [ rdr'
  | i <- [n..]
  , let rdr' = mkVarUnqual $ mkFastString $ baseName ++ show i
  , not $ rdr' `elemFVs` fvs
  ]
  where
    (ds, rest) = span isDigit $ reverse $ occNameString $ occName rdr

    baseName = reverse rest

    -- We build with -Wall -Werror, and there is a warning about how `head` is
    -- partial. Using `head` is safe here because the list is infinite, so the
    -- nil case is impossible. Define our own to avoid the warning.
    headNoWarn (x:_) = x
    headNoWarn _ = error "headNoWarn: impossible!"

    n :: Int
    n | null ds = 1
      | otherwise = read (reverse ds) + 1
