--{-# OPTIONS_GHC -fplugin=Linearity.Plugin.Solver #-}

{-# LANGUAGE DataKinds, KindSignatures, TypeFamilies, GADTs, TypeOperators,
    FlexibleInstances, MultiParamTypeClasses, PolyKinds, TypeApplications,
    InstanceSigs, UndecidableInstances, FlexibleContexts, FunctionalDependencies,
    ConstraintKinds, PatternSynonyms, RebindableSyntax, AllowAmbiguousTypes,
    ScopedTypeVariables, StandaloneKindSignatures, StandaloneDeriving, 
    PartialTypeSignatures, TypeFamilyDependencies, TemplateHaskell, LambdaCase, BlockArguments, RankNTypes #-}

module Files where

import Prelude hiding (Monad(..), read, length)
import System.Random
import qualified Prelude as P
import Data.Kind (Constraint, Type)
import Unsafe.Coerce (unsafeCoerce)
import GHC.TypeLits (TypeError, ErrorMessage(..))
import Control.Concurrent (myThreadId)
import GHC.Types (Any)
import Linearity.Core
import Linearity.Types (Vector(..), HList(..), Contains, Ref, Take, Evolve, Append, Len, Lookup, Drop, Replace, Nat(..), SNat(..)
                       , getS, lenS, appendS, ENat, unsafeCreate, unsafeUncover, Apply, Reverse, Reverse1, Map, MapR, MapR1)
import Linearity.Generator (makeFunc)
import Linearity.Embed
import Control.Monad (liftM2)
import qualified System.IO as IO

ifThenElse True a _ = a
ifThenElse False _ b = b

data IOModeT = ReadModeT | WriteModeT | ReadWriteModeT
type FileState = Maybe IOModeT
type FileEffectState = [FileState]

type IOMode :: IOModeT -> Type
data IOMode m where
  ReadMode :: IOMode ReadModeT
  WriteMode :: IOMode WriteModeT
  ReadWriteMode :: IOMode ReadWriteModeT

getReal :: forall m. IOMode m -> IO.IOMode
getReal ReadMode = IO.ReadMode
getReal WriteMode = IO.WriteMode
getReal ReadWriteMode = IO.ReadWriteMode

type CanRead :: IOModeT -> Constraint
class CanRead a
instance CanRead ReadModeT
instance CanRead ReadWriteModeT

type CanWrite :: IOModeT -> Constraint
class CanWrite a
instance CanWrite WriteModeT
instance CanWrite ReadWriteModeT

type Handle :: Nat -> Type
data Handle n where
    Handle :: IO.Handle -> Handle n

type FileOperation :: Operation FileEffectState 
data FileOperation p q x where
  Open 
    :: String -> IOMode m -> FileOperation p (Append p (Just m)) (Handle (Len p))
  Read 
    :: (Lookup p n ~ Just m, CanRead m) 
    => Handle n -> Int -> FileOperation p p String
  Write 
    :: (Lookup p n ~ Just m, CanWrite m) 
    => Handle n -> String -> FileOperation p p ()
  Size 
    :: (Lookup p n ~ Just m)
    => Handle n -> FileOperation p p Integer
  Close 
    :: (Lookup p n ~ Just m) 
    => Handle n -> FileOperation p (Replace p n Nothing) ()

type CheckNothingAux :: Nat -> FileEffectState -> Constraint
class CheckNothingAux n xs | n -> xs
instance CheckNothingAux Z '[]
instance (CheckNothingAux n xs) => CheckNothingAux (S n) (Nothing ': xs)

type CheckNothing :: FileEffectState -> Constraint
type CheckNothing p = CheckNothingAux (Len p) p

type FileScope :: Scope FileEffectState
data FileScope p p' q' q x x' where
  Isolate 
    :: (CheckNothing q) 
    => FileScope p '[] q p a a

type FileEffect = MkEffect1 FileOperation FileScope

void :: (IFunctor f) => f i j a -> f i j ()
void = imap (const ())

when :: (IMonad m) => Bool -> m i i () -> m i i ()
when False _ = return ()
when True a  = a `seq` a

assist1 :: (IMonad m) => [a] -> (a -> m i i ()) -> m i i ()
assist1 [x] f
  = f x
assist1 (x:xs) f
  = f x >>= \c -> assist1 xs f

assist2 :: (IMonad m) => [a] -> (a -> m i i c) -> m i i [c]
assist2 [] f
  = return []
assist2 (x:xs) f
  = f x >>= \c -> (assist2 xs f >>= \cs -> return (c:cs))

makeFunc ''FileEffect ''FileOperation
isolate s = injectS @FileEffect Isolate s

runFile
  :: (MemberAux (FindEffect Embed sig) Embed sig, CheckNothing q)
  => ITree (FileEffect :- sig) ('[] :+ ps) (q :+ qs) a
  -> ITree sig ps qs a
runFile = runFileH

runFileH
  :: (MemberAux (FindEffect Embed sig) Embed sig)
  => ITree (FileEffect :- sig) (p :+ ps) (q :+ qs) a
  -> ITree sig ps qs a
runFileH (Pure a) = return a
runFileH (Impure (Oinl (Open s m)) c)
  = do
      handle <- injectIO (IO.openFile s (getReal m))
      runFileH (c (Handle handle))
runFileH (Impure (Oinl (Read (Handle handle) n)) c)
  = do
      v <- assist2 [0..n] (const (injectIO (IO.hGetChar handle)))
      runFileH (c v)
runFileH (Impure (Oinl (Write (Handle handle) v)) c)
  = do
      injectIO (IO.hPutStr handle v)
      runFileH (c ())
runFileH (Impure (Oinl (Size (Handle handle))) c)
  = do
      size <- injectIO (IO.hFileSize handle)
      runFileH (c size)
runFileH (Impure (Oinl (Close (Handle handle))) c)
  = do
      injectIO (IO.hClose handle)
      runFileH (c ())

example = runIO . runFile $ do
  handle <- open "test.txt" ReadWriteMode
  write handle "dsfdsdsf"
  close handle
  return ()

--f :: (Member FileEffect u a c i d, _) => ITree u c d ()
f :: (_) => ITree u c d ()
f = do
  handle <- open "presentation.tex" WriteMode 
  write handle "Fin"
  close handle
  return ()