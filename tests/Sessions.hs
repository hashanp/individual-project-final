{-# OPTIONS_GHC -fplugin=Linearity.Plugin.Solver #-}

{-# LANGUAGE DataKinds, KindSignatures, TypeFamilies, GADTs, TypeOperators,
    FlexibleInstances, MultiParamTypeClasses, PolyKinds, TypeApplications,
    InstanceSigs, UndecidableInstances, FlexibleContexts, FunctionalDependencies,
    ConstraintKinds, PatternSynonyms, RebindableSyntax, AllowAmbiguousTypes,
    ScopedTypeVariables, StandaloneKindSignatures, StandaloneDeriving, 
    PartialTypeSignatures, TypeFamilyDependencies, TemplateHaskell #-}

module Sessions where

import Linearity.Core
import Linearity.Embed
import Linearity.Types (Vector(..), HList(..), Sub, Lookup2, Contains, Ref, Take, Evolve, Append, Len, Lookup, Drop, Replace, Nat(..), SNat(..)
                       , getS, lenS, appendS, Map, Apply)
import Linearity.Generator (makeFunc)

import Prelude hiding (Monad(..), truncate)
import qualified Prelude as P
import Data.Tuple (swap)
import Control.Monad (void, liftM2)
import System.Random
import Data.Kind (Constraint, Type)
import Control.Concurrent.Chan (Chan, newChan, writeChan, readChan)
import GHC.Types (Any)
import Unsafe.Coerce (unsafeCoerce)

ifThenElse True a _ = a
ifThenElse False _ b = b

type CNat :: Nat -> Type
data CNat n where
  CNat :: Chan Any -> Chan Any -> CNat n

data ChannelType where
  EndT :: ChannelType 
  SendT :: a -> ChannelType -> ChannelType
  RecvT :: a -> ChannelType -> ChannelType
  ChoiceT :: ChannelType -> ChannelType -> ChannelType
  OfferT :: ChannelType -> ChannelType -> ChannelType
  SendChannelT :: [ChannelType] -> ChannelType -> ChannelType
  RecvChannelT :: [ChannelType] -> ChannelType -> ChannelType
  RecT :: ChannelType -> ChannelType
  RecCallT :: Nat -> ChannelType

type Dual :: ChannelType -> ChannelType
type family Dual i = o | o -> i where
  Dual EndT = EndT
  Dual (SendT a b) = RecvT a (Dual b)
  Dual (RecvT a b) = SendT a (Dual b)
  Dual (SendChannelT a b) = RecvChannelT a (Dual b)
  Dual (RecvChannelT a b) = SendChannelT a (Dual b)
  Dual (ChoiceT a b) = OfferT (Dual a) (Dual b)
  Dual (OfferT a b) = ChoiceT (Dual a) (Dual b)
  Dual (RecT a) = RecT (Dual a)
  Dual (RecCallT a) = RecCallT a

type Channel = Maybe ([ChannelType], Bool)
type SessionState = [Channel]

type NNat :: Nat -> Type
data NNat n = Dummy

data ForkScope a where
  ScopeIn  :: ForkScope Channel
  ScopeOut :: ForkScope Channel

type instance Apply ScopeIn (Just '( '[p], True)) = Just '( '[Dual p], False)
type instance Apply ScopeIn (Just '( _, False)) = Nothing
type instance Apply ScopeOut (Just '( p, _)) = Just '( p, False)
type instance Apply ScopeOut Nothing = Nothing

type MakeSureZeroAux :: Nat -> SessionState -> Constraint
class MakeSureZeroAux n ns | n -> ns
instance MakeSureZeroAux Z '[]
instance (MakeSureZeroAux n xs) => MakeSureZeroAux (S n) (Nothing ': xs)

type MakeSureZero :: SessionState -> Constraint
type MakeSureZero xs = MakeSureZeroAux (Len xs) xs

type SessionOperation :: Operation SessionState
data SessionOperation p q cnt where
  Create 
    :: SessionOperation a (Append a (Just '( '[p], True))) (CNat (Len a))
  Close
    :: (Lookup a n ~ Just '(EndT ': xs, False))
    => CNat n -> SessionOperation a (Replace a n Nothing) ()
  Send 
    :: (Lookup a n ~ Just '( ((SendT t p) ': xs), False)) 
    => CNat n 
    -> t 
    -> SessionOperation a (Replace a n (Just '(p ': xs, False))) ()
  Recv
    :: forall t a n i p xs. (Lookup a n ~ Just '((RecvT t p) ': xs, False))
    => CNat n 
    -> SessionOperation a (Replace a n (Just '(p ': xs, False))) t
  ChooseLeft
    :: (Lookup a n ~ Just '((ChoiceT p1 p2) ': xs, False)) 
    => CNat n 
    -> SessionOperation a (Replace a n (Just '(p1 ': xs, False))) ()
  ChooseRight
    :: (Lookup a n ~ Just '((ChoiceT p1 p2) ': xs, False)) 
    => CNat n 
    -> SessionOperation a (Replace a n (Just '(p2 ': xs, False))) ()
  SendChannel
    :: (Lookup a n ~ Just '((SendChannelT p1 p2) ': xs, False), Lookup a v ~ Just '(p1, False)) 
    => CNat n
    -> CNat v
    -> SessionOperation a (Replace (Replace a v Nothing) n (Just '(p2 ': xs, False))) ()
  RecvChannel
    :: (Lookup a n ~ Just '(((RecvChannelT p1 p2) ': xs), False))
    => CNat n
    -> SessionOperation a (Append (Replace a n (Just '(p2 ': xs, False))) (Just '(p1, False))) (CNat (Len a))
  Rec
    :: (Lookup a n ~ Just '((RecT x) ': xs, False))
    => CNat n
    -> SessionOperation a (Replace a n (Just '(x ': (RecT x) ': xs, False))) (NNat (S (Len xs)))
  RecCall
    :: (Lookup a n ~ Just '((RecCallT t) ': xs, False), Sub t (Len xs) ~ k)
    => CNat n
    -> NNat t
    -> SessionOperation a (Replace a n (Just '(Drop xs k, False))) ()

type SessionScope :: Scope SessionState
data SessionScope p p' q' q x x' where
  Fork :: (MakeSureZero q) => SessionScope p (Map ScopeIn p) q (Map ScopeOut p) () ()

type SessionAlternative :: DualScope SessionState
data SessionAlternative p p1 q1 p2 q2 q where
  Offer 
    :: (Lookup p n ~ Just '((OfferT p1 p2) ': xs, False)) 
    => CNat n 
    -> SessionAlternative p (Replace p n (Just '(p1 ': xs, False))) q (Replace p n (Just '(p2 ': xs, False))) q q

type Session = 'MkEffect SessionOperation SessionScope SessionAlternative

create 
  :: forall u a c i d p. (Member Session u a c i d, Evolve c i (Append a (Just '( '[p], True))) d)
  => ITree u c d (CNat (Len a))
create = inject @Session (Create @a @p) $ return

recv :: forall t u i a c n p d xs.
    (Member Session u a c i d, Lookup a n ~ Just '((RecvT t p) ': xs, False), Evolve c i (Replace a n (Just '(p ': xs, False))) d)
  => CNat n 
  -> ITree u c d t
recv n = inject @Session (Recv n) $ return

makeFunc ''Session ''SessionOperation

offer 
  :: (Member Session u a c i d
     , Lookup a n ~ Just '((OfferT p1 p2) ': xs, False)
     , Evolve c i (Replace a n (Just '(p1 ': xs, False))) ps1
     , Evolve c i (Replace a n (Just '(p2 ': xs, False))) ps2
     , Contains i (q :: SessionState) d, Evolve c i q d)
  => CNat n
  -> ITree u ps1 d x
  -> ITree u ps2 d x
  -> ITree u c d ()
offer n s1 s2 = injectD @Session (Offer n) s1 s2

fork s = injectS @Session Fork s

runSession
  :: (MemberAux (FindEffect Embed sig) Embed sig, MakeSureZero q)
  => ITree (Session :- sig) ('[] :+ ps) (q :+ qs) a
  -> ITree sig ps qs a
runSession = runSessionH False

instance Functor (Vector n) where
  fmap :: (a -> b) -> Vector n a -> Vector n b
  fmap f EmptyS = EmptyS
  fmap f (ConsS x xs) = ConsS (f x) (fmap f xs)

natToInt :: SNat n -> Int
natToInt SZero = 0
natToInt (SSucc n) = 1 + natToInt n

get :: Bool -> CNat n -> Chan Any
get True (CNat a _) = a
get False (CNat _ b) = b

runSessionH
  :: (MemberAux (FindEffect Embed sig) Embed sig)
  => Bool
  -> ITree (Session :- sig) (p :+ ps) (q :+ qs) a
  -> ITree sig ps qs a
runSessionH b (Pure a) = return a
runSessionH b (Impure (Oinl Create) c) 
  = do 
      chan <- injectIO (liftM2 CNat newChan newChan)  
      runSessionH b (c $ chan)
runSessionH b (Impure (Oinl (Send a t)) c)
  = do
      injectIO (writeChan (unsafeCoerce (get (not b) a)) t)
      runSessionH b (c ()) 
runSessionH b (Impure (Oinl (Recv a)) c)
  = do 
      a <- injectIO (readChan (unsafeCoerce (get b a))) 
      runSessionH b (c a)
runSessionH b (Impure (Oinl (ChooseLeft a)) c)
  = do
      unused <- injectIO (writeChan (unsafeCoerce (get (not b) a) :: Chan Bool) True) 
      runSessionH b (c ())
runSessionH b (Impure (Oinl (ChooseRight a)) c)
  = do 
      unused <- injectIO (writeChan (unsafeCoerce (get (not b) a) :: Chan Bool) False) 
      runSessionH b (c ())
runSessionH b (Impure (Oinl (SendChannel a d)) c)
  = do 
      unused <- injectIO (writeChan (unsafeCoerce (get (not b) a)) d)
      runSessionH b (c ()) 
runSessionH b (Impure (Oinl (RecvChannel a)) c)
  = do 
      chan <- injectIO (readChan (unsafeCoerce (get b a) :: Chan (CNat a)))
      runSessionH b (c $ chan)
runSessionH b (DualScope (Dinl (Offer a)) c1 c2 c)
  = do 
      result <- injectIO (readChan (unsafeCoerce (get b a) :: Chan Bool) {-:: IO Bool-})
      if result 
        then runSessionH b (c1 >> unsafeCoerce c)
        else runSessionH b (c2 >> unsafeCoerce c)
runSessionH b (Scope (Sinl Fork) s c)
  = do
      injectFork (runSessionH (not b) (unsafeCoerce s)) 
      runSessionH b $ c ()
runSessionH b (Impure (Oinl (Rec _)) c)
  = runSessionH b (c Dummy)
runSessionH b (Impure (Oinl (RecCall _ _)) c)
  = runSessionH b (c ())
runSessionH b (Impure (Oinl (Close _)) c)
  = do
      runSessionH b (c ())
runSessionH b (Other op c) = Impure op (fmap (runSessionH b) c)
{-runSessionH l (OtherS op c a) = Scope op (runSessionH l c) (runSessionH l a)
runSessionH l (OtherA op c1 c2) = Alternation op (runSessionH l c1) (runSessionH l c2)-}

{-example2 = runIO . runSession $ do
  m <- create
  fork $ do
    v <- obtain m
    return ()
  give m "Hi"
  return "Bye"-}

example7 
  :: (Member Session u a c i d, _)
  => CNat n -> ITree u c d ()
example7 a = do
  v <- rec a
  j <- injectIO (getStdRandom (randomR @Int (1,30)))
  if j > 2 then do
    chooseLeft a
    --injectIO (print j)
    send a j
    recCall a v
    example7 a
  else do
    chooseRight a
    close a
  return ()

example8
  :: (Member Session u a c i d, _)
  => CNat n -> ITree u c d ()
example8 a = do
  v <- rec a
  offer a
    ( do
        k <- recv a
        injectIO (putStrLn (show k))
        recCall a v
        example8 a
    )
    ( do
        injectIO (putStrLn "Goodbye!")
        close a
    )

example9 = runIO . runSession $ do
  m <- create
  fork $ example8 m
  example7 m

example5 = runIO . runSession $ do
  m <- create
  fork $ do
    recv m
    send m "Hello"
    close m
  send m "Hi"
  v <- recv m
  close m
  return "Bye"


example3 = runIO . runSession $ do
  m <- create
  fork $ do
    k <- create
    fork $ do
      p <- recvChannel k
      send p 4
      close p
      close k
    l <- recv {-@String-} m
    offer m (recv m) (recv m)
    sendChannel k m
    close k
  send m "Hello"
  chooseLeft m
  send m 10
  v <- recv {-@Int-} m 
  close m
  return v

{-
example4 = runIO . runSession $ do
  k <- create
  fork $ do
    k2 <- create
    fork $ do
      give k2 5
      return ()
    obtain k2
    give k "hi"
    return ()
  t <- obtain k
  return t


--debug = injectIO . putStrLn

example6 = runIO . runSession $ do
  m <- create
  fork $ do
    --debug "One Thread"
    proffer m (give m "Hello") (give m 4)
  --debug "Another Thread"
  chooseLeft m
  v <- obtain m
  return v
-}

