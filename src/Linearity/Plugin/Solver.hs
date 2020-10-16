{-# LANGUAGE TupleSections, LambdaCase #-}

module Linearity.Plugin.Solver
  ( plugin )
where

import Prelude hiding (init, (<>))
import Data.Maybe (mapMaybe, fromJust, fromMaybe, catMaybes, listToMaybe)
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Control.Monad ((>=>))
import Data.Function (on)
import Data.List (groupBy)
import Data.Tuple (swap)
import RepType (typePrimRep)

import Plugins (Plugin (..), defaultPlugin)
import TcRnTypes (TcPlugin(..), TcPluginResult (..))
import TcPluginM  (TcPluginM, tcPluginIO, getTopEnv, newWanted)
import Constraint (Ct(..), Xi, CtLoc, ctEvidence, ctLoc, ctPred, mkNonCanonical)
import Panic (panicDoc)
import TyCon (TyCon, isPromotedDataCon, isInjectiveTyCon)
import Class (Class)
import Outputable (empty, interppSP, showSDocUnsafe, ppr, parens, brackets, interpp'SP, Outputable, text, (<>), comma, space)
import Predicate (classifyPredType, Pred(..), EqRel(..), mkPrimEqPred, mkClassPred)
import TyCoRep (Type (..), UnivCoProvenance(..), Coercion(Refl))
import Coercion (mkUnivCo, Role(..))
import CoreSyn (Expr(Cast))
import qualified CoreSyn as C
import TcEvidence (EvTerm(..), evCoercion)
import Var (Var)
import Name (Name)
import Type (mkTyConApp)
import DataCon (promoteDataCon, DataCon, dataConWorkId)
import TysWiredIn (boolTy, promotedTrueDataCon, charTy, charDataCon)
import TysPrim (charPrimTy)
import Literal (Literal(LitChar, LitRubbish), absentLiteralOf)

import Linearity.Plugin.Common

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = const (Just myPlugin) }

myPlugin :: TcPlugin
myPlugin =
  TcPlugin { tcPluginInit  = buildState
           , tcPluginSolve = solve
           , tcPluginStop  = stop
           }

stop :: State -> TcPluginM ()
stop _ = do
--  tcPluginIO $ putStrLn "---stop---"
  return ()

getNum :: Int -> OpType
getNum 0 = OpApp OpZero []
getNum x = OpApp OpSucc [getNum (x - 1)]

improveAux :: OpType -> OpType
improveAux (OpApp OpAdvance [sub, sup, ps, i, OpApp OpGet [sub', sup', i', ps']])
  | [sub, sup, ps, i] == [sub', sup', ps', i'] = ps
improveAux (OpApp OpGet [_, sup, i, OpApp OpAdvance [_, sup', _, i', p]])
  | [sup, i] == [sup', i'] = p
improveAux (OpApp OpAdvance [sub, sup, OpApp OpAdvance [sub', sup', ps, i', _], i, x])
  | [sub, sup, i] == [sub', sup', i'] = OpApp OpAdvance [sub, sup, ps, i, x]
{-improveAux (OpApp OpLookup [a, OpMultiAppend a' base (x:xs), OpApp OpLen [a'', base']])
  | a == a' && a' == a'' && base == base' = x-}
improveAux (OpApp OpLookup [a, OpMultiAppend a' base xs, OpShift a'' base' i])
  | {-a == a' && a' == a'' &&-} base == base' && i < length xs = xs !! i
improveAux (OpMultiAppend a (OpMultiAppend a' base xs) ys)
  | a == a' = OpMultiAppend a base (xs ++ ys)
improveAux (OpApp OpReplace [a, OpMultiAppend a' base xs, OpShift a'' base' i, x])
  | {-a == a' && a' == a'' &&-} base == base' && i < length xs = OpMultiAppend a base (take i xs ++ [x] ++ drop (i + 1) xs)
improveAux (OpApp OpReplace [a, OpMultiAppend a' rbase@(OpApp OpMap [_, _, _, base]) xs, OpShift a'' base' i, x])
  | {-a == a' && a' == a'' &&-} base == base' && i < length xs = OpMultiAppend a rbase (take i xs ++ [x] ++ drop (i + 1) xs)

improveAux (OpApp OpReplace [a, OpMultiAppend a' rbase@(OpApp OpReplace [a''', OpApp OpMap [_, _, _, base], i', x']) xs, OpShift a'' base' i, x])
  | {-a == a' && a' == a'' &&-} base == base' && i < length xs = OpMultiAppend a rbase (take i xs ++ [x] ++ drop (i + 1) xs)
improveAux (OpApp OpSub [OpShift a xs i, OpShift a' xs' i'])
  | a == a' && xs == xs' && i <= i' = getNum (i' - i) 
improveAux (OpApp OpReplace [a, OpApp OpReplace [a', base, i', x'], i, x])
  | {-a == a' &&-} i' == i = OpApp OpReplace [a, base, i, x]
improveAux (OpApp OpLookup [a, OpApp OpReplace [a', _, i', x'], i])
  | {-a == a' &&-} i == i' = x'
improveAux (OpApp OpReplace [a, OpMultiAppend a' (OpApp OpReplace [a''', base, c, d]) xs, OpShift a'' base' i, x])
  | {-a == a' && a' == a'' &&-} base == base' && i < length xs = OpMultiAppend a (OpApp OpReplace [a''', base, c, d]) (take i xs ++ [x] ++ drop (i + 1) xs)
improveAux (OpApp OpLookup [a, OpMultiAppend a' (OpApp OpReplace [a''', base, _, _]) xs, OpShift a'' base' i])
  | {-a == a' && a' == a'' &&-} base == base' && i < length xs = xs !! i
improveAux (OpApp OpLookup [a, OpMultiAppend a' (OpApp OpReplace [a''', OpApp OpMap [_, _, _, base], _, _]) xs, OpShift a'' base' i])
  | {-a == a' && a' == a'' &&-} base == base' && i < length xs = xs !! i
{-improveAux (OpApp OpLookup [a, OpMultiAppend a' (OpApp OpMap [_, a''', _, base]) xs, OpShift a'' base' i])
  | {-a == a' && a' == a'' &&-} base == base' && i < length xs = xs !! i-}
improveAux (OpApp OpLookup [a, OpMultiAppend a' (OpApp OpReplace [a''', base, i', x]) xs, i])
  | {-a == a' && a' == a'' &&-} i == i' = x
improveAux (OpApp OpReplace [a, OpMultiAppend a' (OpApp OpReplace [a''', base, i', _]) xs, i, x])
  | {-a == a' && a' == a'' &&-} i == i' = OpMultiAppend a' (OpApp OpReplace [a''', base, i, x]) xs
improveAux (OpApp OpMapR [a, b, c, d, OpApp OpMap [a', b', c', d']])
  | d == d' = d
improveAux (OpApp OpMapR1 [a, b, c, d, OpApp OpMap [a', b', c', d']])
  | d == d' = d
-- Inefficient, n^2 problem here :(
--improveAux (OpApp OpLen [a, OpMultiAppend a' base [x]])
--  | a == a' = OpApp OpSucc [OpApp OpLen [a, base]]
improveAux (OpApp OpMap [a, b, c, OpMultiAppend b' base xs])
  = OpMultiAppend b' (OpApp OpMap [a, b, c, base]) (map (\d -> OpApp OpApply [a, b, c, d]) xs)
improveAux (OpApp OpMap [a, b, c, OpApp OpReplace [b', base, i, x]])
  = OpApp OpReplace [b', OpApp OpMap [a, b, c, base], i, OpApp OpApply [a, b, c, x]]
improveAux (OpApp OpMapR [a, b, c, OpMultiAppend b' base xs, OpMultiAppend b'' base' xs'])
  | length xs == length xs' 
     = OpMultiAppend b' (OpApp OpMapR [a, b, c, base, base']) (zipWith (\d e -> OpApp OpReverse [a, b, c, d, e]) xs xs')
improveAux (OpApp OpMapR1 [a, b, c, OpMultiAppend b' base xs, OpMultiAppend b'' base' xs'])
  | length xs == length xs' 
     = OpMultiAppend b' (OpApp OpMapR1 [a, b, c, base, base']) (zipWith (\d e -> OpApp OpReverse1 [a, b, c, d, e]) xs xs')
improveAux (OpApp OpMapR [a, b, c, OpApp OpReplace [b', base, i, x], OpApp OpReplace [b'', base', i', x']])
  | i == i'
     = OpApp OpReplace [b', OpApp OpMapR [a, b, c, base, base'], i, OpApp OpReverse [a, b, c, x, x']]
improveAux (OpApp OpMapR1 [a, b, c, OpApp OpReplace [b', base, i, x], OpApp OpReplace [b'', base', i', x']])
  | i == i'
     = OpApp OpReplace [b', OpApp OpMapR1 [a, b, c, base, base'], i, OpApp OpReverse1 [a, b, c, x, x']]
improveAux (OpShift a (OpMultiAppend a' base xs) i) 
  = OpShift a base (i + length xs)
improveAux (OpShift a (OpApp OpReplace [a', base, _, _]) i)
  {-| a == a'-} = OpShift a base i
improveAux (OpApp OpDrop [a, OpMultiAppend a' base xs, OpShift a'' base' 0])
  | a == a' && a' == a'' && base == base' = OpList a xs
improveAux (OpApp OpTake [a, base, OpShift a'' base' 0])
  | a == a'' && base == base' = base
improveAux (OpApp OpTake [a, OpMultiAppend a' base xs, OpShift a'' base' 0])
  | a == a' && a' == a'' && base == base' = base
improveAux (OpApp OpTake [a, OpMultiAppend a' (OpApp OpReplace [a''', base, _, _]) xs, OpShift a'' base' 0])
  | {-a == a' && a' == a'' &&-} base == base' = base
improveAux (OpApp OpTake [a, OpMultiAppend a' rbase@(OpApp OpReplace [a''', OpApp OpMap [_, _, _, base], _, _]) xs, OpShift a'' base' i])
  | {-a == a' && a' == a'' &&-} base == base' && i <= length xs = OpMultiAppend a' rbase (take i xs)
improveAux (OpApp OpReverse [a, b, c, d, OpApp OpApply [a', b', c', d']])
  | d == d' = d
improveAux (OpApp OpReverse1 [a, b, c, d, OpApp OpApply [a', b', c', d']])
  | d == d' = d
improveAux a = a

removeSingle :: OpType -> OpType
removeSingle (OpApp OpAppend [a, OpMultiAppend a' base xs, x])
  | a == a' = OpMultiAppend a' base (xs ++ [x])
removeSingle (OpApp OpAppend [a, base, x])
  = OpMultiAppend a base [x]
{-removeSingle (OpShift a (OpMultiAppend a' base xs) i)
  | a == a' = OpShift a base (i + length xs)-}
removeSingle (OpApp OpLen [a, base])
  = OpShift a base 0
removeSingle (OpApp OpSucc [OpShift a b i])
  = OpShift a b (i + 1)
removeSingle (OpApp OpNil [t]) = OpList t []
removeSingle (OpApp OpCons [a, x, OpList a' xs])
  {-| a == a'-} = OpList a (x:xs)
removeSingle a = a
--removeSingle (OpApp )

improve = improveDown improveAux
improve' = improveDown removeSingle

improveDown :: (OpType -> OpType) -> OpType -> OpType
improveDown cnt (OpApp f args)
  = cnt (OpApp f args')
  where args' = map (improveDown cnt) args
improveDown cnt (OpMultiAppend x base args)
  = cnt (OpMultiAppend x base' args')
  where base' = improveDown cnt base
        args' = map (improveDown cnt) args 
improveDown cnt (OpShift a b i)
  = cnt (OpShift a' b' i)
  where a' = improveDown cnt a
        b' = improveDown cnt b
improveDown cnt (OpList a xs)
  = cnt (OpList a' xs')
  where a' = improveDown cnt a
        xs' = map (improveDown cnt) xs
improveDown cnt a = cnt a

deconvertConstraint :: State -> OpConstraint -> [Type]
deconvertConstraint st c
  = case c of 
      OpEquality t _ _ -> map (\(t1, t2) -> mkPrimEqPred (deconvert st t1) (deconvert st t2)) t
      OpContains a c i sub sup _ -> [mkClassPred (fromJust $ lookup OpGet s') (map (deconvert st) [sub, sup, i, a, c])]
      OpEvolve c d sub sup i x _ -> [mkClassPred (fromJust $ lookup OpAdvance s') (map (deconvert st) [sub, sup, OpVar c, i, x, OpVar d])]
      OpRef sup a b -> [mkPrimEqPred boolTy boolTy] -- [mkClassPred (fromJust $ lookup OpZero s') (map (deconvert st) [sup, OpVar a, OpVar b])] -- error "Should not be here!"
      OpNothing -> error "should not be here"
  where s' = map swap (getClass st)

buildMappingVar :: [Ct] -> [(Var, Var)]
buildMappingVar = 
  mapMaybe (\case 
             (CTyEqCan _ v1 (TyVarTy v2) NomEq) -> Just (v2, v1)
             _ -> Nothing)

buildMappingFunc :: State -> [Ct] -> [(Var, OpType)]
buildMappingFunc s = 
  mapMaybe (\case
              (CFunEqCan _ tc args v) -> Just (v, convert s (TyConApp tc args))
--              (CDictCan _ cl [a, b, c, (TyVarTy v), e] _) -> fmap (\x -> (v, OpApp x (map (convert s) [a, b, c, e]))) $ lookup cl (getClass s)
              _ -> Nothing)

{-
 - Type Definitions
 -}

data OpConstraint
  = OpEquality [(OpType, OpType)] Bool Bool -- a ~ b: substitute flag & change flag
  | OpContains OpType OpType OpType OpType OpType Bool -- a, c, i, sub, sup
  | OpEvolve Var Var OpType OpType OpType OpType Bool -- c, d, sub, sup, i, x
  | OpRef OpType Var Var
  | OpNothing
  deriving Eq

instance Outputable OpConstraint where
  ppr OpNothing = text "OpNothing"
  ppr (OpRef _ v1 v2) = text "OpRef" <> parens (ppr v1 <> comma <> space <> ppr v2)
  ppr (OpEquality t _ _) = interppSP (map (\(t1, t2) -> ppr t1 <> text " ~ " <> ppr t2) t)
  ppr (OpEvolve c d sub sup i x _) 
    = text "OpEvolve" 
      <> parens (
          ppr c <> comma <> space 
          <> ppr d <> comma <> space 
          <> ppr sub <> comma <> space 
          <> ppr sup <> comma <> space 
          <> ppr i <> comma <> space <> ppr x)
  ppr (OpContains a c i sub sup _)
    = text "OpContains"
      <> parens (
          ppr a <> comma <> space 
          <> ppr c <> comma <> space 
          <> ppr i <> comma <> space
          <> ppr sub <> comma <> space
          <> ppr sup)

{-
 - Simplification Passes
 -}

nextSimplify :: [Var] -> Map Var OpConstraint -> OpConstraint -> OpConstraint
nextSimplify v prev initial@(OpEvolve c' d' sub' sup' i' x' _)
  = case Map.lookup c' prev of
      Just (OpEvolve c d sub sup i x _)
        -> if {-c' /= d' &&-} (c', i') == (d, i) && c /= c' {-&& c `elem` v-}
            then OpEvolve c d' sub sup i x' True
            else initial
      _ -> initial
nextSimplify _ _ x = x

evolveSimplify :: Map Var OpConstraint -> OpConstraint -> OpConstraint
evolveSimplify prev initial@(OpEvolve c' d' sub' sup' i' (OpVar x') _)
  = case Map.lookup x' prev of
      Just (OpContains (OpVar a) c i sub sup _)
        -> if (c, i, a) == (OpVar c', i', x')
            then OpEquality [(OpVar d', OpVar c')] True True
            else initial
      _ -> initial
-- Does this (the above equation) actually do anything?
evolveSimplify prev initial@(OpContains a (OpVar c) i sub sup _)
  = case Map.lookup c prev of
      Just (OpEvolve _ d sub' sup' i' x _)
        -> if (c, i) == (d, i')
            then OpEquality [(a, x)] True True
            else initial
      _ {-Nothing-}
        -> initial
evolveSimplify _ x = x

substSimplify :: Map Var OpConstraint -> OpConstraint -> OpConstraint
substSimplify prev x
  = case x of
      OpEquality t st ch -> OpEquality (map (\(t1, t2) -> (t1, subst' (getVars t1) t2)) t) st ch
      OpEvolve c d sub sup i x ch -> OpEvolve c d sub sup i (subst' [] x) ch
      x -> x
  where subst' :: [Var] -> OpType -> OpType
        subst' = improveDown . subst
        subst :: [Var] -> OpType -> OpType
        subst bad (OpVar v) = fromMaybe (OpVar v) $ find bad v
        subst _ x = x
        find :: [Var] -> Var -> Maybe OpType
        find bad v 
          | v `elem` bad = Nothing
          | otherwise = case Map.lookup v prev of
                   Just (OpEquality [(t1, t2)] True _) -> Just t2
                   _ -> Nothing

majorSimplify :: OpConstraint -> OpConstraint
majorSimplify (OpEquality t st ch)
  = OpEquality t''' st (ch || changed)
  where t' = map (\(t1, t2) -> (improve' t1, improve' t2)) t
        t'' = map (\(t1, t2) -> (improve t1, improve t2)) t'
        t''' = map canBeFixed t''
        changed = t' /= t'''
        canBeFixed (t1, OpApp OpReplace [a, t1', i, x])
          | t1 == t1' = (x, OpApp OpLookup [a, t1, i])
        canBeFixed x = x
majorSimplify (OpEvolve c d sub sup i x ch)
  = OpEvolve c d sub sup i x'' (ch || changed)
  where x' = improve' x
        x'' = improve x'
        changed = False -- x'' /= x'
majorSimplify x = x

simplify :: [Var] -> Map Var OpConstraint -> OpConstraint -> OpConstraint
simplify v prev 
  = breakdownComplete
    . majorSimplify
    . substSimplify prev 
    . nextSimplify v prev
    . evolveSimplify prev

breakdown :: (OpType, OpType) -> [(OpType, OpType)]
breakdown (OpVar v, OpVar v')
  | v == v' = []
breakdown (OpApp (OpOther ta) args, OpApp (OpOther tb) args')
  | ta == tb && isInjectiveTyCon ta Nominal = zip args args' >>= breakdown
breakdown (a, b) = [(a, b)]

breakdownComplete :: OpConstraint -> OpConstraint
breakdownComplete (OpEquality t st ch) = OpEquality (t >>= breakdown) st ch 
breakdownComplete x = x

extract :: OpConstraint -> Map Var OpConstraint
{-extract ct@(OpEvolve c d _ _ _ _ _)
  | c /= d = Map.singleton d ct
extract ct@(OpContains (OpVar a) _ _ _ _ _)
  = Map.singleton a ct-}
{-extract (OpEquality (OpVar v) (OpVar v') _ _)
  | v == v' = Map.empty-}
extract ct@(OpEquality t True _)
  = Map.fromList $ mapMaybe helper t
  where helper a@(OpVar v, t1) = Just $ (v, OpEquality [a] True False)
        helper _ = Nothing
{-extract (OpEquality (OpApp (OpOther ta) args) (OpApp (OpOther tb) args') True _)
  | ta == tb && isInjectiveTyCon ta Nominal = Map.unions . map extract $ zipWith (\a b -> OpEquality a b True False) args args'-}
extract x = Map.empty --[x]

special :: OpConstraint -> Maybe Var
special (OpRef _ v _) = Just v
special _ = Nothing

special' :: OpConstraint -> Maybe Var
special' (OpRef _ _ v) = Just v
special' _ = Nothing


convertEvolveToAdvance :: [OpConstraint] -> OpConstraint -> OpConstraint
convertEvolveToAdvance prev (OpEvolve c d sub sup i x _)
  | c `elem` possible' && not (d `elem` possible'') = OpEquality [(OpVar d, OpApp OpAdvance [sub, sup, OpVar c, i, x])] True True
  where possible' = mapMaybe special prev
        possible'' = mapMaybe special' prev
{-convertEvolveToAdvance prev (OpRef _ _ _)
  | not (null possible) = OpNothing
  where possible = mapMaybe special prev-}
convertEvolveToAdvance _ x = x

{-
 - Conversion Passes
 -}

createMore :: [OpConstraint] -> Map Var OpType
createMore = Map.fromList . mapMaybe helper
  where helper all@(OpContains a (OpVar c) _ _ _ _) = Just (c, a)
        helper _ = Nothing

bigOp :: [Var] -> [OpConstraint] -> [OpConstraint] -> (Map Var OpConstraint, [OpConstraint])
bigOp [x] xs givens = (xs', xs'')
  where base = createDatabase xs
        change initial@(OpEvolve a b c d e f g) = (b, OpEvolve x b c d e f g)
        (base', toFix) = processDatabase base x
        xs' = Map.fromList $ map (change . (xs !!)) $ base'
        containsMap = createMore (xs ++ givens)
        xs'' = map tryToFix (zip xs [0..])
        tryToFix ((OpEvolve _ d  _ _ _ x ch), n)
          | n `elem` toFix && d `Map.member` containsMap = OpEquality [(fromJust (Map.lookup d containsMap), x)] False True 
        tryToFix (ct, _) = ct
bigOp _ xs _ = (Map.empty, xs)

createDatabase :: [OpConstraint] -> Map Var [(Var, Int)]
createDatabase xs = Map.fromList . map fit . groupBy ((==) `on` key) . catMaybes . zipWith combine [0..] . map f $ xs
  where f :: OpConstraint -> Maybe (Var, Var)
        f (OpEvolve c d _ _ _ _ _) = Just (c, d)
        f _ = Nothing
        combine :: Int -> Maybe (Var, Var) -> Maybe (Var, Var, Int)
        combine z (Just (x, y)) = Just (x, y, z)
        combine _ _ = Nothing
        key :: (Var, Var, Int) -> Var
        key (a, b, c) = a
        fit :: [(Var, Var, Int)] -> (Var, [(Var, Int)])
        fit initial@((x, _, _):_) = (x, map mit initial)
        mit :: (Var, Var, Int) -> (Var, Int)
        mit (x, y, z) = (y, z)

lookup' :: (Ord a) => a -> Map a [b] -> [b]
lookup' a b
  = fromMaybe [] $ Map.lookup a b

processDatabase :: Map Var [(Var, Int)] -> Var -> ([Int], [Int])
processDatabase base x = (a', b)
  where (a, b) = traverseDatabase base (Map.singleton x (-1)) [] (lookup' x base)
        a' = map snd $ Map.toList $ Map.withoutKeys a (Set.singleton x)

traverseDatabase :: Map Var [(Var, Int)] -> Map Var Int -> [Int] -> [(Var, Int)] -> (Map Var Int, [Int])
traverseDatabase _ a b [] = (a, b)
traverseDatabase base seen toBeRemoved ((x,y):xs)
  | x `Map.member` seen = traverseDatabase base seen (y:toBeRemoved) xs
  | otherwise = let (a, b) = traverseDatabase base (Map.insert x y seen) toBeRemoved (lookup' x base) in
                  traverseDatabase base a b xs

handle :: State -> Ct -> Maybe OpConstraint
handle st ct 
  = case classifyPredType (ctPred ct) of
      EqPred NomEq a b -> Just $ OpEquality [(convert st a, convert st b)] True False
      ClassPred cl args -> handleClass st cl args
      _ -> Nothing

handleClass :: State -> Class -> [Type] -> Maybe OpConstraint
handleClass st cl args
  = case (op, args) of 
      (Just OpGet, [sub, sup, i, a, c]) 
        -> Just $ OpContains (convert st a) (convert st c) (convert st i) (convert st sub) (convert st sup) False
      (Just OpAdvance, [sub, sup, TyVarTy c, i, x, TyVarTy d]) 
        -> Just $ OpEvolve c d (convert st sub) (convert st sup) (convert st i) (convert st x) False
      (Just OpZero, [sup, TyVarTy c, TyVarTy d])
        -> Just $ OpRef (convert st sup) c d
      _ -> Nothing
  where op = lookup cl (getClass st)

{-
 - Preparation Phases
 -}

getDirectiveVars :: OpType -> [Var]
getDirectiveVars (OpVar v) = [v]
getDirectiveVars (OpApp (OpOther t) args)
  | isPromotedDataCon t = args >>= getDirectiveVars
getDirectiveVars _ = []

getVars :: OpType -> [Var]
getVars (OpVar v) = [v]
getVars (OpApp _ args)
  = args >>= getVars
getVars (OpShift a b _) 
  = [a, b] >>= getVars
getVars (OpMultiAppend a b c)
  = (a:b:c) >>= getVars
getVars _ = []

{-getSource :: OpConstraint -> [Var]
getSource (OpEquality t1 t2 _ _)
  = getDirectiveVars t1
getSource (OpEvolve c d sub sup i x _)
  = [d]
getSource (OpContains a c i sub sup _)
  = getDirectiveVars a
getSource _
   = []-}

{-getDestination :: OpConstraint -> [Var]
getDestination (OpEquality t1 t2 _ _)
  = getVars t2
getDestination (OpEvolve c d sub sup i x _)
  = c : getVars x ++ getVars sub ++ getVars sup ++ getVars i ++ getVars x
getDestination (OpContains a c i sub sup _)
  = getVars c ++ getVars i ++ getVars sub ++ getVars sup
getDestination _ = []-}

align :: OpConstraint -> OpConstraint
align (OpEquality t st ch) = OpEquality (map alignHelper t) st ch
align x = x

alignHelper :: (OpType, OpType) -> (OpType, OpType)
alignHelper (t1, t2)
  | null t2' && not (null t2'') = (t1, t2)
  | otherwise = (t2, t1)
  where t1' = getDirectiveVars t1
        t2' = getDirectiveVars t2
        t1'' = getVars t1
        t2'' = getVars t2

getChangeFlags :: [OpConstraint] -> [Bool]
getChangeFlags = map hasChanged

hasChanged :: OpConstraint -> Bool
hasChanged (OpEquality _ _ ch) = ch
hasChanged (OpContains _ _ _ _ _ ch) = ch
hasChanged (OpEvolve _ _ _ _ _ _ ch) = ch
hasChanged (OpRef _ _ _) = True -- error "Should not be here!"
hasChanged _ = True

{-
 - Main Stuff
 -}

zeroChange :: Bool -> OpConstraint -> OpConstraint
zeroChange t (OpEquality t' st _) = OpEquality t' st t
zeroChange t (OpContains a b c d e _) = OpContains a b c d e t
zeroChange t (OpEvolve a b c d e f _) = OpEvolve a b c d e f t
zeroChange t x = x

construct :: State -> [Ct] -> [Ct] -> TcPluginM [(Ct, OpConstraint)]
construct st given cts
  = do
      tcPluginIO $ putStrLn $ showSDocUnsafe $ interppSP (map majorSimplify cts')
      tcPluginIO $ putStrLn "more"
      --tcPluginIO $ putStrLn $ showSDocUnsafe $ ppr $ given'''
      --tcPluginIO $ putStrLn $ showSDocUnsafe $ ppr $ (innerConstruct 1 given' cts')
      tcPluginIO $ putStrLn $ showSDocUnsafe $ ppr $ Map.unions $ map extract result'
      --tcPluginIO $ putStrLn $ showSDocUnsafe $ interppSP given''
{-      tcPluginIO $ putStrLn $ showSDocUnsafe $ interppSP special'
      tcPluginIO $ putStrLn "results"
      tcPluginIO $ putStrLn $ showSDocUnsafe $ interppSP $ filter hasChanged result-}
--      tcPluginIO $ putStrLn $ showSDocUnsafe $ ppr given'
--      tcPluginIO $ putStrLn $ showSDocUnsafe $ interppSP $ snd $ constructHelper given' cts'
      return . filter (\(a, b) -> hasChanged b) $ zip old result
  where (old, cts'') = unzip . mapMaybe (keepMaybe (handle st)) $ cts
        cts''' = map ({-otherSimplify st .-} align) cts''
        result' = innerConstruct 5 given' cts'
        result = map (convertEvolveToAdvance given'') result'
        innerConstruct :: Int -> Map Var OpConstraint -> [OpConstraint] -> [OpConstraint]
        innerConstruct 0 _ c = c
        innerConstruct n mapping c 
            | {-or b' || mapping' /= mapping-} otherwise = innerConstruct (n - 1) mapping' {-$ zipWith setChange b''-} c'
            | otherwise = {-zipWith setChange b''-} c
          where (mapping', c') = constructHelper special' mapping ({-zipWith zeroChange (repeat False)-} c)
                b = getChangeFlags c
                b' = getChangeFlags c'
                c'' = zipWith zeroChange (zipWith (||) b b') c'
                --b'' = zipWith (||) b b'
        given'' = mapMaybe (handle st) given
        (given''', cts') = bigOp special' cts''' given''
        given' = Map.unions $ given''':(map extract given'')
        special' = mapMaybe special given''

constructHelper :: [Var] -> Map Var OpConstraint -> [OpConstraint] -> (Map Var OpConstraint, [OpConstraint])
constructHelper _ mapping [] = (mapping, [])
constructHelper v mapping (x:xs)
  = (s, x' : t)
  where x' = simplify v mapping x
        vars = extract {-$ fromMaybe x-} x'
        (s, t) = constructHelper v (Map.union vars mapping) xs

improveHelper' :: (OpType, OpType) -> Maybe (OpType, OpType)
improveHelper' (t1, t2)
--  | t1' == t1 && t2' == t2 = Nothing
  | otherwise = Just (t1', t2')
  where t1' = improve t1
        t2' = improve t2

both f (a, b) = (f a, f b)

turnIntoCt :: State -> (Ct, OpConstraint) -> (EvTerm, Ct)
turnIntoCt st (ct, x)
  | l2 == 0 = (EvExpr (Cast (C.Coercion (Refl boolTy)) ev2), ct)
  | l2 == 1 = (EvExpr (Cast (C.App (C.Var (dataConWorkId charDataCon)) (C.Lit (LitChar 'c'))) ev1), ct)
  | otherwise = error (show (l1, l2, l3))
  where ev1 = mkUnivCo (PluginProv "linearity") Representational (charTy) (ctPred ct)
        ev2 = mkUnivCo (PluginProv "linearity") Representational (mkPrimEqPred boolTy boolTy) (ctPred ct)
        l1 = length $ typePrimRep (charTy)
        l2 = length $ typePrimRep (ctPred ct)
        l3 = length $ typePrimRep (mkPrimEqPred boolTy boolTy)

makeIntoCt :: State -> (Ct, OpConstraint) -> TcPluginM [Ct]
makeIntoCt st (ct, x) = (map mkNonCanonical) <$> mapM (newWanted (ctLoc ct)) (deconvertConstraint st x)

solve :: State -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
solve st given derived wanted = do
  tcPluginIO $ putStrLn "---boulder---"
  tcPluginIO $ putStrLn $ showSDocUnsafe $ interppSP given
  tcPluginIO $ putStrLn $ showSDocUnsafe $ interppSP wanted
--  tcPluginIO $ putStrLn $ showSDocUnsafe $ interppSP vars
  tcPluginIO $ putStrLn "---start---"
  let vars = (buildMappingVar given)
  --let funcs = {-filter (\(a, b) -> isGood b)-} (buildMappingFunc st given)
  --tcPluginIO $ putStrLn $ showSDocUnsafe $ interppSP funcs
--  let funcs2 = (buildMappingFunc2 given)
  --let rel = mapMaybe (\(a, b) -> fmap (a,) $ lookup b funcs) vars
  y <- construct st given wanted
--  let y = mapMaybe (handle st) $ wanted
--let y = (mapMaybe (keepMaybe (improve rel advance)) wanted)
--  tcPluginIO $ putStrLn $ showSDocUnsafe $ interppSP $ map (improve rel advance) wanted
--  let y = mapMaybe (keepMaybe pipeline) $ wanted
  let res = map (turnIntoCt st) y
  b <- concat <$> mapM (makeIntoCt st) {-(filter (\(a, b) -> b /= OpNothing)-} y--(y >>= simplifyHelper)
--  let (a, b') = unzip res
--  let (a, b) = ([], [])
  {-if null res
    then 
      return ()
    else do-}
  if not (null res)
    then do
      tcPluginIO $ putStrLn "---here---"
      tcPluginIO $ putStrLn $ "what is proven:\n " ++ (showSDocUnsafe (interppSP (map snd res)))
      tcPluginIO $ putStrLn $ "what needs to be proven:\n " ++ (showSDocUnsafe (interppSP (map snd y)))
    else
      return ()
--     tcPluginIO $ putStrLn $ "what needs to be proven:\n " ++ (showSDocUnsafe (interppSP b))
--  tcPluginIO $ putStrLn $ showSDocUnsafe $ interppSP $ map (improve rel advance) wanted
  return $ TcPluginOk res b
--  return $ TcPluginOk [] []
