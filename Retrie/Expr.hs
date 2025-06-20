-- Copyright (c) 2025 Andrew Farmer
-- Copyright (c) 2020-2024 Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module Retrie.Expr
  ( bitraverseHsConDetails
  , getUnparened
  , grhsToExpr
  , mkApps
  , mkConPatIn
  , mkEpAnn
  , mkHsAppsTy
  , mkLams
  , mkLet
  , mkLoc
  , mkLocA
  , mkLocatedHsVar
  , mkVarPat
  , mkTyVar
  , parenify
  , parenifyT
  , parenifyP
  , patToExpr
  -- , patToExprA
  -- , setAnnsFor
  , unparen
  , unparenP
  , unparenT
  , wildSupply
  ) where

import Control.Monad
import Control.Monad.State.Lazy

import Retrie.ExactPrint
import Retrie.Fixity
import Retrie.GHC
import Retrie.SYB
import Retrie.Types

-------------------------------------------------------------------------------

mkLocatedHsVar :: Monad m => LocatedN RdrName -> TransformT m (LHsExpr GhcPs)
mkLocatedHsVar (L l n) = do
  mkLocA (SameLine 0)  (HsVar noExtField (L (setMoveAnchor (SameLine 0) l) n))

-- TODO: move to ghc-exactprint
setMoveAnchor :: (Monoid an) => DeltaPos -> SrcAnn an -> SrcAnn an
setMoveAnchor dp (SrcSpanAnn EpAnnNotUsed l)
  = SrcSpanAnn (EpAnn (dpAnchor l dp) mempty emptyComments) l
setMoveAnchor dp (SrcSpanAnn (EpAnn (Anchor a _) an cs) l)
  = SrcSpanAnn (EpAnn (Anchor a (MovedAnchor dp)) an cs) l

-- TODO: move to ghc-exactprint
dpAnchor :: SrcSpan -> DeltaPos -> Anchor
dpAnchor l dp = Anchor (realSrcSpan l) (MovedAnchor dp)

-------------------------------------------------------------------------------

-- setAnnsFor :: (Data e, Monad m)
--            => Located e -> [(KeywordId, DeltaPos)] -> TransformT m (Located e)
-- setAnnsFor e anns = modifyAnnsT (M.alter f (mkAnnKey e)) >> return e
--   where f Nothing  = Just annNone { annsDP = anns }
--         f (Just a) = Just a { annsDP = M.toList
--                                      $ M.union (M.fromList anns)
--                                                (M.fromList (annsDP a)) }

mkLoc :: (Data e, Monad m) => e -> TransformT m (Located e)
mkLoc e = do
  L <$> uniqueSrcSpanT <*> pure e

-- ++AZ++:TODO: move to ghc-exactprint
mkLocA :: (Data e, Monad m, Monoid an)
  => DeltaPos -> e -> TransformT m (LocatedAn an e)
mkLocA dp e = mkLocAA dp mempty e

-- ++AZ++:TODO: move to ghc-exactprint
mkLocAA :: (Data e, Monad m) => DeltaPos -> an -> e -> TransformT m (LocatedAn an e)
mkLocAA dp an e = do
  l <- uniqueSrcSpanT
  let anc = Anchor (realSrcSpan l) (MovedAnchor dp)
  return (L (SrcSpanAnn (EpAnn anc an emptyComments) l) e)


-- ++AZ++:TODO: move to ghc-exactprint
mkEpAnn :: Monad m => DeltaPos -> an -> TransformT m (EpAnn an)
mkEpAnn dp an = do
  anc <- mkAnchor dp
  return $ EpAnn anc an emptyComments

mkAnchor :: Monad m => DeltaPos -> TransformT m (Anchor)
mkAnchor dp = do
  l <- uniqueSrcSpanT
  return (Anchor (realSrcSpan l) (MovedAnchor dp))

-------------------------------------------------------------------------------

mkLams
  :: [LPat GhcPs]
  -> LHsExpr GhcPs
  -> TransformT IO (LHsExpr GhcPs)
mkLams [] e = return e
mkLams vs e = do
  ancg <- mkAnchor (SameLine 0)
  ancm <- mkAnchor (SameLine 0)
  let
    ga = GrhsAnn Nothing (AddEpAnn AnnRarrow (EpaDelta (SameLine 1) []))
    ang = EpAnn ancg ga emptyComments
    anm = EpAnn ancm [(AddEpAnn AnnLam (EpaDelta (SameLine 0) []))] emptyComments
    L l (Match _ ctxt pats (GRHSs cs grhs binds)) = mkMatch LambdaExpr vs e emptyLocalBinds
    grhs' = case grhs of
      [L lg (GRHS _ guards rhs)] -> [L lg (GRHS ang guards rhs)]
      _ -> fail "mkLams: lambda expression can only have a single grhs!"
  matches <- mkLocA (SameLine 0) [L l (Match anm ctxt pats (GRHSs cs grhs' binds))]
  let
    mg =
#if __GLASGOW_HASKELL__ < 908
      mkMatchGroup Generated matches
#else
      mkMatchGroup (Generated SkipPmc) matches
#endif
  mkLocA (SameLine 1) $ HsLam noExtField mg

mkLet :: Monad m => HsLocalBinds GhcPs -> LHsExpr GhcPs -> TransformT m (LHsExpr GhcPs)
mkLet EmptyLocalBinds{} e = return e
mkLet lbs e = do
  an <- mkEpAnn (DifferentLine 1 5) NoEpAnns
  let tokLet = L (TokenLoc (EpaDelta (SameLine 0) [])) HsTok
      tokIn = L (TokenLoc (EpaDelta (DifferentLine 1 1) [])) HsTok
  le <- mkLocA (SameLine 1) $ HsLet an tokLet lbs tokIn e
  return le

mkApps :: MonadIO m => LHsExpr GhcPs -> [LHsExpr GhcPs] -> TransformT m (LHsExpr GhcPs)
mkApps e []     = return e
mkApps f (a:as) = do
  -- lift $ liftIO $ debugPrint Loud "mkApps:f="  [showAst f]
  f' <- mkLocA (SameLine 0) (HsApp noAnn f a)
  mkApps f' as

-- GHC never generates HsAppTy in the parser, using HsAppsTy to keep a list
-- of types.
mkHsAppsTy :: Monad m => [LHsType GhcPs] -> TransformT m (LHsType GhcPs)
mkHsAppsTy [] = error "mkHsAppsTy: empty list"
mkHsAppsTy (t:ts) = foldM (\t1 t2 -> mkLocA (SameLine 1) (HsAppTy noExtField t1 t2)) t ts

mkTyVar :: Monad m => LocatedN RdrName -> TransformT m (LHsType GhcPs)
mkTyVar nm = do
  tv <- mkLocA (SameLine 1) (HsTyVar noAnn NotPromoted nm)
  -- _ <- setAnnsFor nm [(G AnnVal, DP (0,0))]
  (tv', _) <- swapEntryDPT tv nm
  return tv'

mkVarPat :: Monad m => LocatedN RdrName -> TransformT m (LPat GhcPs)
mkVarPat nm = cLPat <$> mkLocA (SameLine 1) (VarPat noExtField nm)

-- type HsConPatDetails p = HsConDetails (HsPatSigType (NoGhcTc p)) (LPat p) (HsRecFields p (LPat p))

mkConPatIn
  :: Monad m
  => LocatedN RdrName
  -> HsConPatDetails GhcPs
  -- -> HsConDetails Void (LocatedN RdrName) [RecordPatSynField GhcPs]
  -> TransformT m (LPat GhcPs)
mkConPatIn patName params = do
  p <- mkLocA (SameLine 0) $ ConPat noAnn patName params
  -- setEntryDPT p (DP (0,0))
  return p

-------------------------------------------------------------------------------

-- Note [Wildcards]
-- We need to invent unique binders for wildcard patterns and feed
-- them in as quantified variables for the matcher (they will match
-- some expression and be discarded). We do this hackily here, by
-- generating a supply of w1, w2, etc variables, and filter out any
-- other binders we know about. However, we should also filter out
-- the free variables of the expression, to avoid capture. Haven't found
-- a free variable computation on HsExpr though. :-(

type PatQ m = StateT ([RdrName], [RdrName]) (TransformT m)

newWildVar :: Monad m => PatQ m RdrName
newWildVar = do
  (s, u) <- get
  case s of
    (r:s') -> do
      put (s', r:u)
      return r
    [] -> error "impossible: empty wild supply"

wildSupply :: [RdrName] -> [RdrName]
wildSupply used = wildSupplyP (`notElem` used)

wildSupplyP :: (RdrName -> Bool) -> [RdrName]
wildSupplyP p =
  [ r | i <- [0..]
      , let r = mkVarUnqual (mkFastString ('w' : show (i :: Int)))
      , p r ]

patToExpr :: MonadIO m => LPat GhcPs -> PatQ m (LHsExpr GhcPs)
patToExpr orig = case dLPat orig of
  Nothing -> error "patToExpr: called on unlocated Pat!"
  Just lp@(L _ p) -> do
    e <- go p
    lift $ transferEntryDP lp e
  where
    -- go :: Pat GhcPs -> PatQ m (LHsExpr GhcPs)
    go WildPat{} = do
      w <- newWildVar
      v <- lift $ mkLocA (SameLine 1) w
      lift $ mkLocatedHsVar v
    go (ConPat _ con ds) = conPatHelper con ds
    go (LazyPat _ pat) = patToExpr pat
    go (BangPat _ pat) = patToExpr pat
    go (ListPat _ ps) = do
      ps' <- mapM patToExpr ps
      lift $ do
        an <- mkEpAnn (SameLine 1)
                      (AnnList Nothing (Just (AddEpAnn AnnOpenS d0)) (Just (AddEpAnn AnnCloseS d0)) [] [])
        el <- mkLocA (SameLine 1) $ ExplicitList an ps'
        -- setAnnsFor el [(G AnnOpenS, DP (0,0)), (G AnnCloseS, DP (0,0))]
        return el
    go (LitPat _ lit) = lift $ do
      -- lit' <- cloneT lit
      mkLocA (SameLine 1) $ HsLit noAnn lit
    go (NPat _ llit mbNeg _) = lift $ do
      -- L _ lit <- cloneT llit
      e <- mkLocA (SameLine 1) $ HsOverLit noAnn (unLoc llit)
      negE <- maybe (return e) (mkLocA (SameLine 0) . NegApp noAnn e) mbNeg
      -- addAllAnnsT llit negE
      return negE
    go (ParPat an _ p' _) = do
      p <- patToExpr p'
      let tokLP = L (TokenLoc (EpaDelta (SameLine 0) [])) HsTok
          tokRP = L (TokenLoc (EpaDelta (SameLine 0) [])) HsTok
      lift $ mkLocA (SameLine 1) (HsPar an tokLP p tokRP)
    go SigPat{} = error "patToExpr SigPat"
    go (TuplePat an ps boxity) = do
      es <- forM ps $ \pat -> do
        e <- patToExpr pat
        return $ Present noAnn e
      lift $ mkLocA (SameLine 1) $ ExplicitTuple an es boxity
    go (VarPat _ i) = lift $ mkLocatedHsVar i
    go AsPat{} = error "patToExpr AsPat"
    go NPlusKPat{} = error "patToExpr NPlusKPat"
    go SplicePat{} = error "patToExpr SplicePat"
    go SumPat{} = error "patToExpr SumPat"
    go ViewPat{} = error "patToExpr ViewPat"

conPatHelper :: MonadIO m
             => LocatedN RdrName
             -> HsConPatDetails GhcPs
             -> PatQ m (LHsExpr GhcPs)
conPatHelper con (InfixCon x y) =
  lift . mkLocA (SameLine 1)
               =<< OpApp <$> pure noAnn
                         <*> patToExpr x
                         <*> lift (mkLocatedHsVar con)
                         <*> patToExpr y
-- TODO(xich): Properly handle tyargs here!
conPatHelper con (PrefixCon _tyargs xs) = do
  f <- lift $ mkLocatedHsVar con
  as <- mapM patToExpr xs
  -- lift $ lift $ liftIO $ debugPrint Loud "conPatHelper:f="  [showAst f]
  lift $ mkApps f as
conPatHelper _ _ = error "conPatHelper RecCon"

-------------------------------------------------------------------------------

grhsToExpr :: LGRHS GhcPs (LHsExpr GhcPs) -> LHsExpr GhcPs
grhsToExpr (L _ (GRHS _ [] e)) = e
grhsToExpr (L _ (GRHS _ (_:_) e)) = e -- not sure about this

-------------------------------------------------------------------------------

precedence :: FixityEnv -> HsExpr GhcPs -> Maybe Fixity
#if __GLASGOW_HASKELL__ < 908
precedence _        (HsApp {})       = Just $ Fixity (SourceText "HsApp") 10 InfixL
#else
precedence _        (HsApp {})       = Just $ Fixity (SourceText (fsLit "HsApp")) 10 InfixL
#endif
precedence fixities (OpApp _ _ op _) = Just $ lookupOp op fixities
precedence _        _                = Nothing

parenify
  :: Monad m => Context -> LHsExpr GhcPs -> TransformT m (LHsExpr GhcPs)
parenify Context{..} le@(L _ e)
  | needed ctxtParentPrec (precedence ctxtFixityEnv e) && needsParens e = do
    let tokLP = L (TokenLoc (EpaDelta (SameLine 0) [])) HsTok
        tokRP = L (TokenLoc (EpaDelta (SameLine 0) [])) HsTok
     in mkParen' (getEntryDP le) (\an -> HsPar an tokLP (setEntryDP le (SameLine 0)) tokRP)
  | otherwise = return le
  where
           {- parent -}               {- child -}
    needed (HasPrec (Fixity _ p1 d1)) (Just (Fixity _ p2 d2)) =
      p1 > p2 || (p1 == p2 && (d1 /= d2 || d2 == InfixN))
    needed NeverParen _ = False
    needed _ Nothing = True
    needed _ _ = False

getUnparened :: Data k => k -> k
getUnparened = mkT unparen `extT` unparenT `extT` unparenP

-- TODO: what about comments?
unparen :: LHsExpr GhcPs -> LHsExpr GhcPs
unparen expr = case expr of
  L _ (HsPar _ _ e _)
    -- see Note [Sections in HsSyn] in GHC.Hs.Expr
    | L _ SectionL{} <- e -> expr
    | L _ SectionR{} <- e -> expr
    | otherwise -> e
  _ -> expr

-- | hsExprNeedsParens is not always up-to-date, so this allows us to override
needsParens :: HsExpr GhcPs -> Bool
needsParens = hsExprNeedsParens (PprPrec 10)

mkParen' :: (Data x, Monad m, Monoid an)
         => DeltaPos -> (EpAnn NoEpAnns -> x) -> TransformT m (LocatedAn an x)
mkParen' dp k = do
  let an = NoEpAnns
  l <- uniqueSrcSpanT
  let anc = Anchor (realSrcSpan l) (MovedAnchor (SameLine 0))
  pe <- mkLocA dp (k (EpAnn anc an emptyComments))
  return pe

mkParenTy :: (Data x, Monad m, Monoid an)
         => DeltaPos -> (EpAnn AnnParen -> x) -> TransformT m (LocatedAn an x)
mkParenTy dp k = do
  let an = AnnParen AnnParens d0 d0
  l <- uniqueSrcSpanT
  let anc = Anchor (realSrcSpan l) (MovedAnchor (SameLine 0))
  pe <- mkLocA dp (k (EpAnn anc an emptyComments))
  return pe

-- This explicitly operates on 'Located (Pat GhcPs)' instead of 'LPat GhcPs'
-- because it is applied at that type by SYB.
parenifyP
  :: Monad m
  => Context
  -> LPat GhcPs
  -> TransformT m (LPat GhcPs)
parenifyP Context{..} p@(L _ pat)
  | IsLhs <- ctxtParentPrec
  , needed pat =
    let tokLP = L (TokenLoc (EpaDelta (SameLine 0) [])) HsTok
        tokRP = L (TokenLoc (EpaDelta (SameLine 0) [])) HsTok
     in mkParen' (getEntryDP p) (\an -> ParPat an tokLP (setEntryDP p (SameLine 0)) tokRP)
  | otherwise = return p
  where
    needed BangPat{}                          = False
    needed LazyPat{}                          = False
    needed ListPat{}                          = False
    needed LitPat{}                           = False
    needed ParPat{}                           = False
    needed SumPat{}                           = False
    needed TuplePat{}                         = False
    needed VarPat{}                           = False
    needed WildPat{}                          = False
    needed (ConPat _ _ (PrefixCon _ []))      = False
    needed _                                  = True

parenifyT
  :: Monad m => Context -> LHsType GhcPs -> TransformT m (LHsType GhcPs)
parenifyT Context{..} lty@(L _ ty)
  | needed ty =
      mkParenTy (getEntryDP lty) (\an -> HsParTy an (setEntryDP lty (SameLine 0)))
  | otherwise = return lty
  where
    needed t = case ctxtParentPrec of
      HasPrec (Fixity _ prec InfixN) -> hsTypeNeedsParens (PprPrec prec) t
      -- We just assume we won't have mixed 'FixityDirection's for 'HsType',
      -- this is not true for 'HsFunTy' (@infixr 2@) and 'HsOpTy' (@infixl 2@).
      -- Currently, we will simply always add parens around 'HsOpTy'.
      HasPrec (Fixity _ prec _) -> hsTypeNeedsParens (PprPrec $ prec - 1) t
      IsLhs -> False
      NeverParen -> False

unparenT :: LHsType GhcPs -> LHsType GhcPs
unparenT (L _ (HsParTy _ ty)) = ty
unparenT ty = ty

unparenP :: LPat GhcPs -> LPat GhcPs
unparenP (L _ (ParPat _ _ p _)) = p
unparenP p = p

--------------------------------------------------------------------

bitraverseHsConDetails
  :: Applicative m
  => ([tyarg] -> m [tyarg'])
  -> (arg -> m arg')
  -> (rec -> m rec')
  -> HsConDetails tyarg arg rec
  -> m (HsConDetails tyarg' arg' rec')
bitraverseHsConDetails argt argf _ (PrefixCon tyargs args) =
  PrefixCon <$> (argt tyargs) <*> (argf `traverse` args)
bitraverseHsConDetails _ _ recf (RecCon r) =
  RecCon <$> recf r
bitraverseHsConDetails _ argf _ (InfixCon a1 a2) =
  InfixCon <$> argf a1 <*> argf a2
