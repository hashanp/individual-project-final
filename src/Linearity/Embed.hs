{-# LANGUAGE DataKinds, KindSignatures, TypeFamilies,
      GADTs, TypeOperators, FlexibleInstances,
      MultiParamTypeClasses, PolyKinds, TypeApplications,
      InstanceSigs, UndecidableInstances, FlexibleContexts,
      FunctionalDependencies, ConstraintKinds, PatternSynonyms,
      NoImplicitPrelude, AllowAmbiguousTypes, ScopedTypeVariables,
      StandaloneKindSignatures, BlockArguments, StandaloneDeriving #-}

module Linearity.Embed where

import Linearity.Core hiding (IMonad(..))
import qualified Linearity.Core as Core
import Linearity.Types
import Control.Monad.STM (atomically)
import Control.Concurrent.STM.TMVar (TMVar, newEmptyTMVarIO, putTMVar, takeTMVar)
import Control.Concurrent (forkIO)
import qualified Prelude as P
import GHC.Types (Any)
import Control.Monad (void)
import Prelude
import Unsafe.Coerce (unsafeCoerce)
import System.IO (hFlush, stdout)

type EmbedOperation :: Operation ()
data EmbedOperation p q cnt where
  EmbedOperation :: IO a -> EmbedOperation p p a
  
type EmbedScope :: Scope ()
data EmbedScope p p' q' q x x' where
  EmbedFork :: EmbedScope p p p p a (IO a)

type Embed :: Effect ()
type Embed = MkEffect1 EmbedOperation EmbedScope

runIO :: forall a. ITree (Embed :- Nil) ('() :+ Unit) ('() :+ Unit) a -> IO a
runIO (Pure x) = return x
runIO (Impure (Oinl (EmbedOperation m)) c) = m >>= \t -> hFlush stdout >> (runIO (c t))
runIO (Scope (Sinl EmbedFork) c a)
  = do
      var <- newEmptyTMVarIO 
      forkIO $ do 
        b <- runIO c 
        {-b `seq`-} 
        atomically (putTMVar (var) b)
      runIO (a (atomically (takeTMVar (var))))

injectIO
  :: forall u i c a b.
    (MemberAux (FindEffect Embed u) Embed u) 
  => IO a
  -> ITree u c c a
injectIO m = injectT @Embed (EmbedOperation m) $ Core.return

injectFork
  :: forall u i p ps a.
    (MemberAux (FindEffect Embed u) Embed u) 
  => ITree u ps ps a -> ITree u ps ps (IO a)
injectFork s = injectQ @Embed EmbedFork s 
