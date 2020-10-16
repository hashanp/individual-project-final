{-# OPTIONS_GHC -fplugin=Linearity.Plugin.Solver #-}

{-# LANGUAGE DataKinds, KindSignatures, TypeFamilies,
      GADTs, TypeOperators, FlexibleInstances,
      MultiParamTypeClasses, PolyKinds, TypeApplications,
      InstanceSigs, UndecidableInstances, FlexibleContexts,
      FunctionalDependencies, ConstraintKinds, PatternSynonyms,
      RebindableSyntax, AllowAmbiguousTypes, ScopedTypeVariables,
      StandaloneKindSignatures, BlockArguments, StandaloneDeriving,
      PartialTypeSignatures, RankNTypes, TemplateHaskell #-}

module Storage () where

import Prelude hiding (Monad(..), truncate)
import Data.Kind (Constraint, Type)
import Unsafe.Coerce (unsafeCoerce)
import GHC.TypeLits (TypeError, ErrorMessage(..))
import Linearity.Core
import Linearity.Types (HList(..), Sub, Contains, Ref, Take, Evolve, Append, Len, Lookup, Drop, Replace, Nat(..), SNat(..))
import Linearity.Generator (makeFunc)
import GHC.Types (Any)

type ENat :: Nat -> Type
data ENat n where
  ENat :: Int -> ENat n

zero = ENat @Z 0
one = ENat @(S (Z)) 1 
two = ENat @(S (S (Z))) 2

type StorageState = [(Type, Nat)]

type List :: StorageState -> Type
data List a where
  Empty  :: List '[]
  Cons :: (x :: *) -> List xs -> List ('(x, n) ': xs)

type StorageOperation :: Operation StorageState
data StorageOperation p q x where
  RegisterMany
    :: (Len a ~ k) 
    => ENat n -> b -> StorageOperation a (Append a '(b, n)) (ENat k)
  UseMany
    :: (Lookup i n ~ '(k, m), Sub v m ~ t) 
    => ENat v -> ENat n -> StorageOperation i (Replace i n '(k, t)) k

type StorageScope :: Scope StorageState
data StorageScope p p' q' q x x' where
  Local' :: forall p q' q k a rest. (k ~ Len p, '(q, rest) ~ Split q' k, AllZero rest) => StorageScope p p q' q a a

type StorageEffect = MkEffect1 StorageOperation StorageScope

type Split xs n = '(Take xs n, Drop xs n)

type First :: forall a b. (a, b) -> a
type family First a where
  First '(x, _) = x

type VerifyAux :: StorageState -> Nat -> [Nat]
type family VerifyAux a b where
  VerifyAux '[] i = '[]
  VerifyAux ('(_, Z) : xs) i = VerifyAux xs (S i)
  VerifyAux ('(_, _) : xs) i = (i ': VerifyAux xs (S i))

type VerifyStr :: [Nat] -> ErrorMessage
type family VerifyStr a where
  VerifyStr '[a] = ShowType a :<>: Text " have not been fully consumed in the linear context"
  VerifyStr (a ': as) = ShowType a :<>: Text ", " :<>: VerifyStr as

type VerifyWrapper :: [Nat] -> ()
type family VerifyWrapper as where
  VerifyWrapper '[] = '()
  VerifyWrapper ns = TypeError (Text "Indices " :<>: VerifyStr ns)

type AllZero :: StorageState -> Constraint
type AllZero a = VerifyWrapper (VerifyAux a Z) ~ '()

append :: List a -> b -> ENat n -> List (Append a '(b, n))
append Empty b n = Cons b Empty
append (Cons b' a) b n = Cons b' (append a b n)

replace :: forall t i n. List i -> ENat n -> List (Replace i n t)
replace m _ = unsafeCoerce m

local 
  :: forall p q' q k rest i ps ps' qs' qs u e.
    ('(q, rest) ~ Split q' k, AllZero rest, Member StorageEffect u p ps i qs, Contains i q' qs', k ~ Len p, Evolve qs' i q qs)
  => (ITree u ps qs' e) -> ITree u ps qs e
local = (injectS @StorageEffect) (Local' @p @q' @q @k)

makeFunc ''StorageEffect ''StorageOperation

use 
  :: (Member StorageEffect u a c i d, Lookup a n ~ '(t, k), Evolve c i (Replace a n '(t, Sub (S Z) k)) d)
  => ENat n
  -> ITree u c d t
use = useMany one

register
  :: (Member StorageEffect u a c i d, Len a ~ k, Evolve c i (Append a '(t, S Z)) d)
  => t
  -> ITree u c d (ENat k)
register = registerMany one

type Token c v = forall k. (Lookup c k ~ v) => ENat k

runLinear 
  :: (AllZero j) 
  => ITree (StorageEffect :- sig) ('[] :+ p) (j :+ q) a 
  -> ITree sig p q (a, [Any])
runLinear = runLinearH []

runLinearH 
  :: forall sig i j p q a len. [Any]
  -> ITree (StorageEffect :- sig) (i :+ p) (j :+ q) a 
  -> ITree sig p q (a, [Any])
runLinearH l (Pure a) 
  = return (a, l)
runLinearH l (Impure (Oinl (UseMany _ (ENat i))) cnt) 
  = runLinearH l (cnt (unsafeCoerce (l !! i)))
runLinearH l (Impure (Oinl (RegisterMany _ b)) cnt) 
  = runLinearH (l ++ [unsafeCoerce b]) (cnt $ ENat (length l))
runLinearH a (Other op c) 
  = Impure op (fmap (runLinearH a) c)

example3 :: (Member StorageEffect u a c i c) => {-Token a v ->-} ITree u c c String
example3 {-k-} = do
  local $ do
    i <- register "bob"
    j <- register True
    use i
    use j
--  use k
  return "hi"

example4 :: (Member StorageEffect u a c i d, _) => {-Token a v ->-} ITree u c d String
example4 {-k-} = do
  i <- register "bob"
  j <- register 5
  use i
  use j
--  use k
  return "hi"

{-example :: (_) => _
example = do
  i <- register 10 
  j <- use i
  return j-}

{-main = do
  putStrLn  . fst . run . runLinear $ example4-}
