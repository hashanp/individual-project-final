{-# LANGUAGE DataKinds, KindSignatures, TypeFamilies,
      GADTs, TypeOperators, FlexibleInstances,
      MultiParamTypeClasses, PolyKinds, TypeApplications,
      InstanceSigs, UndecidableInstances, FlexibleContexts,
      FunctionalDependencies, ConstraintKinds, PatternSynonyms,
      NoImplicitPrelude, AllowAmbiguousTypes, ScopedTypeVariables,
      StandaloneKindSignatures, BlockArguments, StandaloneDeriving #-}

module Linearity.Core where

import Prelude hiding (Monad(..), truncate)
import Linearity.Types (HList(..), Evolve, Contains, Ref, Nat(..))
import Data.Kind (Constraint, Type)
import GHC.TypeLits (TypeError, ErrorMessage(..))
import Unsafe.Coerce (unsafeCoerce)

class IFunctor f where
  imap :: (a -> b) -> f i j a -> f i j b

class IMonad m where
  return :: a -> m i i a
  (>>=) :: m i j a -> (a -> m j k b) -> m i k b
  (>>) :: m i j a -> m j k b -> m i k b
  g >> f = g >>= const f

type Operation a = a -> a -> Type -> Type
type Scope a = a -> a -> a -> a -> Type -> Type -> Type
type DualScope a = a -> a -> a -> a -> a -> a -> Type

data Effect a where
  MkEffect :: Operation a -> Scope a -> DualScope a -> Effect a

type MkEffect1 a b = 'MkEffect a b VoidDualScope

type VoidDualScope :: forall a. DualScope a
data VoidDualScope a b c d e f

type GetOperation :: Effect a -> Operation a
type family GetOperation a where
  GetOperation (MkEffect x _ _) = x

type GetScope :: Effect a -> Scope a
type family GetScope a where
  GetScope (MkEffect _ y _) = y

type GetDualScope :: Effect a -> DualScope a
type family GetDualScope a where
  GetDualScope (MkEffect _ _ z) = z

type HListEffect :: [Type] -> Type
data HListEffect k where
  Nil :: HListEffect '[]
  (:-) :: Effect p -> HListEffect ps -> HListEffect (p ': ps)

type ContextOperation :: forall sig. HListEffect sig -> HList sig -> HList sig -> Type -> Type
data ContextOperation a b c d where
  Oinl :: forall a p q as ps cnt. (GetOperation a) p q cnt -> ContextOperation (a :- as) (p :+ ps) (q :+ ps) cnt
  Oinr :: forall a p as ps qs cnt. ContextOperation as ps qs cnt -> ContextOperation (a :- as) (p :+ ps) (p :+ qs) cnt

type ContextScope :: forall sig. HListEffect sig -> HList sig -> HList sig -> HList sig -> HList sig -> Type -> Type -> Type
data ContextScope a b c d e f g where
  Sinl :: forall a p' q' p q as ps x x'. (GetScope a) p p' q' q x x' -> ContextScope (a :- as) (p :+ ps) (p' :+ ps) (q' :+ ps)  (q :+ ps) x x'
  Sinr :: forall a p as ps ps' qs' qs x x'. ContextScope as ps ps' qs' qs x x' -> ContextScope (a :- as) (p :+ ps) (p :+ ps') (p :+ qs') (p :+ qs) x x'

type ContextDualScope :: forall sig. HListEffect sig -> HList sig -> HList sig -> HList sig -> HList sig -> HList sig -> HList sig -> Type
data ContextDualScope a b c d e f g where
  Dinl :: forall a p q p1 q1 p2 q2 as ps. (GetDualScope a) p p1 q1 p2 q2 q 
       -> ContextDualScope (a :- as) (p :+ ps) (p1 :+ ps) (p2 :+ ps) (q1 :+ ps) (q2 :+ ps) (q :+ ps)
  Dinr :: forall a p as ps ps1 qs1 ps2 qs2 qs. ContextDualScope as ps ps1 qs1 ps2 qs2 qs 
       -> ContextDualScope (a :- as) (p :+ ps) (p :+ ps1) (p :+ qs1) (p :+ ps2) (p :+ qs2) (p :+ qs)

type FindEffect :: forall m b. Effect b -> HListEffect m -> Nat
type family FindEffect b m where
  FindEffect a (a :- as) = Z
  FindEffect b (a :- as) = (S (FindEffect b as))
  FindEffect c Nil = TypeError (Text "Effect " :<>: ShowType c :<>: Text " not found in signature")

{-type MemberAux 
  :: forall sub sup. Nat
  -> Effect sub
  -> HListEffect sup
  -> Constraint-}
class MemberAux index sub sup | index sup -> sub where
  inj 
    :: (GetOperation sub) a b cnt 
    -> ContextOperation sup c d cnt
  injS 
    :: (GetScope sub) p p' q' q x x'
    -> ContextScope sup ps ps' qs' qs x x'
  injT 
    :: (GetOperation sub) a a cnt 
    -> ContextOperation sup c c cnt
  injQ 
    :: (GetScope sub) a a a a x x'
    -> ContextScope sup c c c c x x'
  injD 
    :: (GetDualScope sub) p p1 q1 p2 q2 q
    -> ContextDualScope sup ps ps1 qs1 ps2 qs2 qs

instance MemberAux Z a (a :- as) where
  inj = unsafeCoerce Oinl
  injS = unsafeCoerce Sinl
  injT = unsafeCoerce Oinl
  injQ = unsafeCoerce Sinl
  injD = unsafeCoerce Dinl

instance (MemberAux index sub sup) => MemberAux (S index) sub (s :- sup) where
  inj = unsafeCoerce (Oinr . inj @index @sub @sup {- @a @cs @b @ds -} )
  injS = unsafeCoerce (Sinr . injS @index @sub @sup) {- @sub @sup  -}
  injT = unsafeCoerce (Oinr . injT @index @sub @sup)
  injQ = unsafeCoerce (Sinr . injQ @index @sub @sup)
  injD = unsafeCoerce (Dinr . injD @index @sub @sup)

type Member 
  :: forall sub sup. Effect sub 
  -> HListEffect sup 
  -> sub 
  -> HList sup 
  -> Nat
  -> HList sup
  -> Constraint
type Member l u a c i d = (i ~ FindEffect l u, MemberAux i l u, Contains i a c, Ref c d)

{- 
 - f :: Sigma
 - g :: Pi
 - p :: Precondition
 - q :: Postcondition
 - a :: Output
 -}
data ITerm f g h p q a where
  Pure :: a -> ITerm f g h p p a
  Impure :: f p q a -> (a -> ITerm f g h q r b) -> ITerm f g h p r b
  Scope ::  g p p' q' q x x' -> ITerm f g h p' q' x -> (x' -> ITerm f g h q r a) -> ITerm f g h p r a
  DualScope 
    :: h p p1 q1 p2 q2 q 
    -> ITerm f g h p1 q1 x
    -> ITerm f g h p2 q2 x
    -> ITerm f g h q r a
    -> ITerm f g h p r a

instance IFunctor (ITerm f g h) where
  imap :: (a -> b) -> ITerm f g h p q a -> ITerm f g h p q b
  imap f (Pure a) = Pure $ f a
  imap f (Impure o a) = Impure o $ fmap (imap f) a
  imap f (Scope g c a) = Scope g c $ fmap (imap f) a
  imap f (DualScope h c1 c2 a) = DualScope h c1 c2 $ imap f a

instance IMonad (ITerm f g h) where
  return :: a -> ITerm f g h i i a
  return = Pure

  (>>=) :: ITerm f g h i j a -> (a -> ITerm f g h j k b) -> ITerm f g h i k b
  (Pure a) >>= f = f a
  (Impure o a) >>= f = Impure o $ fmap (>>= f) a
  (Scope g c a) >>= f = Scope g c (fmap (>>= f) a)
  (DualScope h c1 c2 a) >>= f = DualScope h c1 c2 ((>>= f) a)

type ITree sig = ITerm (ContextOperation sig) (ContextScope sig) (ContextDualScope sig)

inject 
  :: forall l b u i a c c' d x cnt.
    (Member l u a c i d, Evolve c i b c') 
  => (GetOperation l) a b x -> (x -> ITree u c' d cnt)
  -> ITree u c d cnt
inject = Impure . inj @i

injectS 
  :: forall l u i p p' q' q ps ps' qs' qs x x'.
    (Member l u p ps i qs, Contains i q' qs', Evolve ps i p' ps', Evolve qs' i q qs)
  => (GetScope l) p p' q' q x x' -> ITree u ps' qs' x -> ITree u ps qs x'
injectS m s = Scope (injS @i m) s return

injectT
  :: forall (l :: Effect ()) a u i c d x cnt.
    (MemberAux (FindEffect l u) l u {-a c i c-})
  => (GetOperation l) '() '() x -> (x -> ITree u c d cnt)
  -> ITree u c d cnt
injectT = Impure . injT @(FindEffect l u) @l

injectQ
  :: forall (l :: Effect ()) u i p ps x x'.
    ({-IFunctorable u,-} MemberAux (FindEffect l u) l u {-p ps i ps-})
  => (GetScope l) p p p p x x' -> ITree u ps ps x -> ITree u ps ps x'
injectQ m s = Scope (injQ @(FindEffect l u) @l m) s return

injectD
  :: forall l u i p p1 q1 p2 q2 q ps ps1 qs1 ps2 qs2 qs x.
    (i ~ FindEffect l u, MemberAux i l u, Contains i p ps, Contains i q qs, Evolve ps i p1 ps1, Evolve ps i p2 ps2, Evolve ps i q qs)
  => (GetDualScope l) p p1 q1 p2 q2 q
  -> ITree u ps1 qs1 x
  -> ITree u ps2 qs2 x
  -> ITree u ps qs ()
injectD m s1 s2 = DualScope (injD @(FindEffect l u) @l m) s1 s2 (return ())

run :: ITree Nil Unit Unit a -> a
run (Pure x) = x

pattern Other s c = Impure (Oinr s) c
