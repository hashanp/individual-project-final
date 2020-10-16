{-# LANGUAGE TupleSections #-}

module Linearity.Plugin.Common 
 ( OpFun(..), OpType(..), buildState, convert, deconvert, State(..), keepMaybe )
where

import Prelude hiding ((<>))
import Data.Maybe (fromJust)
import TcPluginM (TcPluginM, lookupOrig, tcLookupTyCon, tcLookupClass, tcLookupId, tcPluginIO, tcLookupDataCon, getTopEnv)
import OccName (mkTcOcc, mkDataOcc)
import Finder (findPluginModule, FindResult(..))
import Module (Module, mkModuleName)
import Outputable (empty, interppSP, ppr, parens, brackets, interpp'SP, Outputable, text, (<>), comma, space)
import TyCon (TyCon)
import Class (Class)
import TyCoRep (Type (..))
import DataCon (promoteDataCon, DataCon)
import Var (Var, Id)
import Type (eqType)
import TysWiredIn (promotedNilDataCon, promotedConsDataCon, promotedTupleDataCon)
import Data.Tuple (swap)
import Panic (panicDoc)
import BasicTypes (Boxity(..))

keepMaybe :: (a -> Maybe b) -> (a -> Maybe (a, b))
keepMaybe f a = fmap (a,) $ f a 

data OpFun
  = OpGet 
  | OpAdvance
  | OpReplace
  | OpLookup
  | OpLen
  | OpAppend
  | OpSucc
  | OpZero
  | OpDrop
  | OpPair
  | OpMap
  | OpMapR
  | OpMapR1
  | OpApply
  | OpSub
  | OpReverse
  | OpReverse1
  | OpCons
  | OpNil
  | OpHCons
  | OpTake
  | OpHList
  | OpPower
  | OpEmpty
  | OpOther TyCon
  deriving Eq

instance Outputable OpFun where
  ppr OpGet = text "Get"
  ppr OpLookup = text "Lookup"
  ppr OpLen = text "Len"
  ppr OpAppend = text "Append"
  ppr OpAdvance = text "Advance"
  ppr OpReplace = text "Replace"
  ppr OpZero = text "Z"
  ppr OpSucc = text "S"
  ppr OpTake = text "Take"
  ppr OpDrop = text "Drop"
  ppr OpPower = text "Power"
  ppr OpPower = text "Empty"
  ppr OpSub = text "OpSub"
  ppr OpCons = text "Cons"
  ppr OpNil = text "Nil"
  ppr OpPair = text "Pair"
  ppr OpMap = text "Map"
  ppr OpMapR = text "MapR"
  ppr OpMapR1 = text "MapR1"
  ppr OpApply = text "Apply"
  ppr OpReverse = text "Reverse"
  ppr OpReverse1 = text "Reverse1"
  ppr OpHCons = text "HCons"
  ppr OpHList = text "HList"
  ppr (OpOther tc) = ppr tc

data OpType
  = OpApp OpFun [OpType]
  | OpVar Var
  | OpLift Type 
  | OpMultiAppend OpType OpType [OpType] -- Contained kind, list, additions
  | OpShift OpType OpType Int
  | OpList OpType [OpType]

instance Eq OpType where
  (OpApp f args) == (OpApp f' args') = f == f' && args == args'
  (OpVar v) == (OpVar v') = v == v'
  (OpLift t) == (OpLift t') = eqType t t'
  (OpMultiAppend a b args) == (OpMultiAppend a' b' args') 
    = a == a' && b == b' && args == args'
  (OpShift a b i) == (OpShift a' b' i')
    = a == a' && b == b' && i == i'
  (OpList a xs) == (OpList a' xs')
    = a == a' && xs == xs'
  _ == _ = False

instance Outputable OpType where
  ppr (OpApp f []) = ppr f
  ppr (OpApp f op) = ppr f <> parens (interpp'SP op)
  ppr (OpVar v) = ppr v
  ppr (OpLift t) = ppr t
  ppr (OpMultiAppend a b args) = text "OpMultiAppend" <> brackets (ppr b) <> parens (interpp'SP args)
  ppr (OpShift a b i) = text "OpShift" <> parens (ppr a <> comma <> space <> ppr b <> comma <> space <> ppr i)
  ppr (OpList a xs) = brackets (interpp'SP xs)

lookupModule :: String -> TcPluginM Module
lookupModule name = do
  hsc_env <- getTopEnv
  found_module <- tcPluginIO $ findPluginModule hsc_env (mkModuleName name)
  case found_module of
    Found _ the_module -> return the_module
    _ -> panicDoc "Unable to find the module" (empty)

lookupTyCon :: Module -> String -> TcPluginM TyCon
lookupTyCon search_module name
  = tcLookupTyCon =<< lookupOrig search_module (mkTcOcc name)

lookupDataCon :: Module -> String -> TcPluginM DataCon
lookupDataCon search_module name
  = tcLookupDataCon =<< lookupOrig search_module (mkDataOcc name)

lookupClass :: Module -> String -> TcPluginM Class
lookupClass search_module name
  = tcLookupClass =<< lookupOrig search_module (mkTcOcc name)

convert :: State -> Type -> OpType
convert s op 
  = case op of
      TyVarTy v -> OpVar v
      TyConApp tc args -> OpApp (convertFun s tc) (map (convert s) args)
      _ -> OpLift op

convertFun :: State -> TyCon -> OpFun
convertFun s tc
  = case lookup tc (getTyCon s) of
      Nothing -> OpOther tc
      Just a -> a

deconvert :: State -> OpType -> Type
deconvert s op
  = case op of
      OpApp fun args -> TyConApp (deconvertFun s fun) (map (deconvert s) args)
      OpVar v -> TyVarTy v
      OpLift t -> t
      OpMultiAppend a b [] -> deconvert s b
      OpMultiAppend a b (x:xs) -> deconvert s (OpMultiAppend a (OpApp OpAppend [a, b, x]) xs)
      OpShift a b 0 -> deconvert s $ OpApp OpLen [a, b]
      OpShift a b c -> deconvert s $ OpApp OpSucc [OpShift a b (c - 1)]
      OpList a [] -> TyConApp promotedNilDataCon [deconvert s a]
      OpList a (x:xs) -> TyConApp promotedConsDataCon [deconvert s a, deconvert s x, deconvert s (OpList a xs)]
 
deconvertFun :: State -> OpFun -> TyCon
deconvertFun s fun
  = case fun of
      OpOther tc -> tc
      _ -> fromJust $ lookup fun s'
  where s' = map swap (getTyCon s)

lookupId :: Module -> String -> TcPluginM Id
lookupId search_module name
  = tcLookupId =<< lookupOrig search_module (mkTcOcc name)

data State = State
  { getTyCon :: [(TyCon, OpFun)]
  , getClass :: [(Class, OpFun)]
  }

buildState :: TcPluginM State
buildState = do
  tcPluginIO $ putStrLn "---init---"
  my_module <- lookupModule  "Linearity.Types"
  prelude <- lookupModule "Data.Type.Equality"
  get <- lookupTyCon my_module "Get"
  advance <- lookupTyCon my_module "Advance"
  lookup <- lookupTyCon my_module "Lookup"
  len <- lookupTyCon my_module "Len"
  append <- lookupTyCon my_module "Append"
  replace <- lookupTyCon my_module "Replace"
  empty <- lookupTyCon my_module "Void"
  lower_zero <- lookupDataCon my_module "Z"
  lower_succ <- lookupDataCon my_module "S"
  drop <- lookupTyCon my_module "Drop"
  take <- lookupTyCon my_module "Take"
  map <- lookupTyCon my_module "Map"
  mapr <- lookupTyCon my_module "MapR"
  mapr1 <- lookupTyCon my_module "MapR1"
  sub <- lookupTyCon my_module "Sub"
  apply <- lookupTyCon my_module "Apply"
  reverse <- lookupTyCon my_module "Reverse"
  reverse1 <- lookupTyCon my_module "Reverse1"
  hlist <- lookupTyCon my_module "HList"
  contains <- lookupClass my_module "Contains"
  evolve <- lookupClass my_module "Evolve"
  ref <- lookupClass my_module "Ref"
  lower_hcons <- lookupDataCon my_module ":+"
  the_thing <- lookupTyCon prelude ":~:"
  let zero = promoteDataCon lower_zero
  let hcons = promoteDataCon lower_hcons
  let succ = promoteDataCon lower_succ
--  pair <- lookupTyCon prelude "(,)"
  let mappingTyCon = [ 
       (get, OpGet)
       , (advance, OpAdvance)
       , (lookup, OpLookup)
       , (len, OpLen)
       , (append, OpAppend)
       , (zero, OpZero)
       , (succ, OpSucc)
       , (replace, OpReplace)
       , (drop, OpDrop)
       , (take, OpTake)
       , (hcons, OpHCons)
       , (sub, OpSub)
       , (promotedConsDataCon, OpCons)
       , (promotedNilDataCon, OpNil)
       , (the_thing, OpPower)
       , (empty, OpEmpty)
      -- , (promotedTupleDataCon Boxed 2, OpPair)
       , (hlist, OpHList)
       , (apply, OpApply)
       , (reverse, OpReverse)
       , (reverse1, OpReverse1)
       , (map, OpMap)
       , (mapr, OpMapR)
       , (mapr1, OpMapR1)
       ]
  let mappingClass = [
       (contains, OpGet)
       , (evolve, OpAdvance)
       , (ref, OpZero)
       ]
  return $ State mappingTyCon mappingClass
