{-# LANGUAGE DataKinds, KindSignatures, TypeFamilies,
      GADTs, TypeOperators, FlexibleInstances,
      MultiParamTypeClasses, PolyKinds, TypeApplications,
      InstanceSigs, UndecidableInstances, FlexibleContexts,
      FunctionalDependencies, ConstraintKinds, PatternSynonyms,
      RebindableSyntax, AllowAmbiguousTypes, ScopedTypeVariables,
      StandaloneKindSignatures, BlockArguments, StandaloneDeriving, TypeFamilyDependencies #-}

module Linearity.Types 
  (HList(..), Vector(..), Advance, Get, Len, Ref, Append, Lookup, Lookup2, Replace, Drop, Take, Nat(..), Contains, Evolve, SNat(..)
  , appendS, lenS, getS, ENat, unsafeCreate, Sub, unsafeUncover, Apply, Reverse, Reverse1, Map, MapR, MapR1)
where

import Prelude (Show, Int)
import Data.Kind (Constraint, Type)
import GHC.TypeLits (TypeError, ErrorMessage(..))
import Unsafe.Coerce (unsafeCoerce)

data Nat = Z | S Nat

type Ref :: forall sup. HList sup -> HList sup -> Constraint
class Ref a b
instance Ref Unit Unit
instance (Ref c d) => Ref (a :+ c) (b :+ d)

type SNat :: Nat -> Type
data SNat n where
  SZero :: SNat Z
  SSucc :: SNat n -> SNat (S n)

type ENat :: Nat -> Type
data ENat n where
  ENat :: a -> ENat n

type Sub :: Nat -> Nat -> Nat
type family Sub a b where
  Sub Z a = a
  Sub (S a) (S b) = Sub a b
  Sub (S a) b = TypeError (Text "Can't do that I'm afraid")

unsafeCreate :: forall a n. a -> ENat n
unsafeCreate = ENat

unsafeUncover :: forall a n. ENat n -> a
unsafeUncover (ENat a) = unsafeCoerce a

deriving instance Show (SNat n)

type Lookup :: [a] -> Nat -> a
type family Lookup a b where
  Lookup '[] _ = TypeError (Text "Could not find index")
  Lookup (_ ': xs) (S n) = Lookup xs n
  Lookup (x ': _) Z = x

type Lookup2 :: [a] -> Nat -> a
type family Lookup2 a b where
  Lookup2 xs i = TypeError (Text "Could not find index in " :<>: ShowType xs :<>: Text " " :<>: ShowType i)

type Len :: [a] -> Nat
type family Len a where
  Len '[] = Z
  Len (x ': xs) = S (Len xs)

type Drop :: [a] -> Nat -> [a]
type family Drop xs n where
  Drop xs Z = xs
  Drop (x ': xs) (S n) = Drop xs n

type Void :: Constraint
type Void = ()

type Apply :: forall k a. k a -> a -> a
type family Apply a b
type Reverse :: forall k a. k a -> a -> a -> a
type family Reverse a b c
type Reverse1 :: forall k a. k a -> a -> a -> a
type family Reverse1 a b c

type Map :: forall k a. k a -> [a] -> [a]
type family Map f a where
  Map f '[] = '[]
  Map f (x ': xs) = (Apply f x) ': (Map f xs)

type MapR :: forall k a. k a -> [a] -> [a] -> [a]
type family MapR f a b where
  MapR f '[] _ = '[]
  MapR f (x ': xs) (y ': ys) = (Reverse f x y) ': (MapR f xs ys)

type MapR1 :: forall k a. k a -> [a] -> [a] -> [a]
type family MapR1 f a b where
  MapR1 f '[] _ = '[]
  MapR1 f (x ': xs) (y ': ys) = (Reverse1 f x y) ': (MapR1 f xs ys)

type Take :: [a] -> Nat -> [a]
type family Take xs n where
  Take _ Z = '[]
  Take (x ': xs) (S n) = x ': (Take xs n)

type Append :: [a] -> a -> [a]
type family Append xs x where
  Append '[] t = t ': '[]
  Append (x ': xs) t = x ': (Append xs t)

type HList :: [Type] -> Type
data HList k where
  Unit :: HList '[]
  (:+) :: p -> HList ps -> HList (p ': ps)

type Advance :: forall sub sup. HList sup -> Nat -> sub -> HList sup
type family Advance xs i v where
  Advance 'Unit _ _ = TypeError ('Text "Well this is problematic")
  Advance (x ':+ xs) 'Z x' = x' ':+ xs
  Advance (x ':+ xs) ('S n) x' = x ':+ (Advance x' n xs)

type Evolve :: forall sub sup. HList sup -> Nat -> sub -> HList sup -> Constraint
class Evolve xs i x xs' | xs i x -> xs' 
instance Evolve (x ':+ xs) Z y (y ':+ xs)
instance (Evolve xs n y ys) => Evolve (x ':+ xs) (S n) y (x ':+ ys)

type Get :: forall sub sup. Nat -> HList sup -> sub
type family Get i xs where
  Get Z (x :+ _) = x
  Get (S n) (_ :+ xs) = Get n xs
  Get _ _ = TypeError (Text "Out of bounds error")

type Replace :: forall m. [m] -> Nat -> m -> [m]
type family Replace xs idx m where
--  Replace '[] m n = Error "Context empty" (Hopefully this isn't possible)
  Replace (x ': xs) Z m = m ': xs
  Replace (x ': xs) (S s) m = x ': (Replace xs s m)

type Contains :: forall sub sup. Nat
  -> sub
  -> HList sup
  -> Constraint
class Contains index sub sup | index sup -> sub
instance Contains 'Z a (a ':+ as)
instance (Contains n a xs) => Contains ('S n) a (x ':+ xs)

type Vector :: Nat -> Type -> Type
data Vector n a where
  EmptyS :: Vector 'Z a
  ConsS :: a -> Vector n a -> Vector ('S n) a

appendS :: Vector n a -> a -> Vector ('S n) a
appendS EmptyS a = ConsS a EmptyS
appendS (ConsS x xs) a = ConsS x (appendS xs a)

getS :: Vector n a -> SNat u -> a
getS (ConsS x _) SZero = x
getS (ConsS _ xs) (SSucc n) = getS xs n

lenS :: Vector n a -> SNat n
lenS EmptyS = SZero
lenS (ConsS _ xs) = SSucc (lenS xs)