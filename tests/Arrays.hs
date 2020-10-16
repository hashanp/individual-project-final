{-# OPTIONS_GHC -fplugin=Linearity.Plugin.Solver #-}

{-# LANGUAGE DataKinds, KindSignatures, TypeFamilies, GADTs, TypeOperators,
    FlexibleInstances, MultiParamTypeClasses, PolyKinds, TypeApplications,
    InstanceSigs, UndecidableInstances, FlexibleContexts, FunctionalDependencies,
    ConstraintKinds, PatternSynonyms, RebindableSyntax, AllowAmbiguousTypes,
    ScopedTypeVariables, StandaloneKindSignatures, StandaloneDeriving, 
    PartialTypeSignatures, TypeFamilyDependencies, TemplateHaskell, LambdaCase, BlockArguments, RankNTypes #-}

module Arrays (partition, example5, example6) where

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
import qualified Data.Array.IO as IO

ifThenElse True a _ = a
ifThenElse False _ b = b

data AccessLevel = N | R | X

type ArrayAccess = (AccessLevel, AccessLevel)

data ArrayResource where
  Array :: a -> ArrayResource 
  Alias :: a -> Nat -> ArrayResource

type ArrayValue = (ArrayResource, ArrayAccess)
type ArrayIndex = [ArrayValue]

type GetType :: ArrayResource -> Type
type family GetType a where
  GetType (Array a) = a
  GetType (Alias a _) = a

type Leq :: AccessLevel -> AccessLevel -> Constraint
class Leq a b
instance Leq a X
instance Leq R R
instance Leq N R
instance Leq N N

type Max :: AccessLevel -> AccessLevel -> AccessLevel
type family Max a b where
  Max X _ = X
  Max _ X = X
  Max R _ = R
  Max _ R = R
  Max _ _ = N

type ArrayState = (ArrayIndex, [Bool])

type ArrayOperation :: Operation ArrayState 
data ArrayOperation p q x where
  Alloc 
    :: Int 
    -> a 
    -> ArrayOperation '(p, w) '(Append p '(Array a, '(X, N)), w) (ENat (Len p))
  Read 
    :: (Lookup p n ~ '(r, '(u, l)), Leq R u)
    => ENat n
    -> Int 
    -> ArrayOperation '(p, w) '(Replace p n '(r, '(u, Max R l)), w) (GetType r)
  DemandWrite 
    :: (Lookup p n ~ '(r, '(X, l))) 
    => ENat n 
    -> ArrayOperation '(p, w) '(Replace p n '(r, '(X, X)), w) ()
  Write 
    :: (Lookup p n ~ '(r, '(X, l))) 
    => ENat n 
    -> Int 
    -> GetType r
    -> ArrayOperation '(p, w) '(Replace p n '(r, '(X, X)), w) ()
  Length 
    :: (Lookup p n ~ '(r, '(u, l)), Leq R u) 
    => ENat n -> ArrayOperation '(p, w) '(Replace p n '(r, '(u, Max R l)), w) Int
  Join 
    :: (Lookup p n1 ~ '(Alias r k, '(X, a1)), Lookup p n2 ~ '(Alias r k, '(X, a2)), Lookup p k ~ '(r', '(N, c))) 
    => ENat n1 
    -> ENat n2
    -> ArrayOperation '(p, w) '(Replace (Replace (Replace p n1 '(Alias r k, '(N, X))) n2 '(Alias r k, '(N, X))) k '(r', '(X, c)), w) ()
  Slice 
    :: (Lookup p n ~ '(r, '(X, a)), Len p ~ k, GetType r ~ r') 
    => ENat n 
    -> Int
    -> ArrayOperation '(p, w) '(Append (Append (Replace p n '(r, '(N, X))) '(Alias r' n, '(X, X))) '(Alias r' n, '(X, X)), w) (ENat k, ENat ('S k))
  Wait
    :: (Lookup w n ~ 'True)
    => Phantom a b n
    -> ArrayOperation '(p, w) '(MapR1 ForkScope p b, Replace w n 'False) a
  
data Phantom a b n = Phantom (ENat n)

type ArrayScope :: Scope ArrayState
data ArrayScope p p' q' q x x' where
  Fork :: ArrayScope '(p, w) '(Map ForkScope p, w) '(q, w2) '(MapR ForkScope p q, Append w 'True) a (Phantom a (Take q (Len p)) (Len w))
  Local :: ArrayScope '(p, w) '(p, w) '(p', w') '(Take p' (Len p), Take w' (Len w)) a a

type ArrayEffect = MkEffect1 ArrayOperation ArrayScope

data Op a where 
  ForkScope :: Op ArrayValue

type instance Apply ForkScope '(r, '(a, _)) = '(r, '(a, N))
type instance Reverse ForkScope '(r, '(_, a)) '(r, '(_, X)) = '(r, '(N, X))
type instance Reverse ForkScope '(r, '(_, a)) '(r, '(_, R)) = '(r, '(R, Max a R))
type instance Reverse ForkScope '(r, '(t, a)) '(r, '(_, N)) = '(r, '(t, a))
type instance Reverse1 ForkScope '(r, '(a, c)) '(r, '(b, _)) = '(r, '(Max a b, c))

void :: (IFunctor f) => f i j a -> f i j ()
void = imap (const ())

when :: (IMonad m) => Bool -> m i i () -> m i i ()
when False _ = return ()
when True a  = a `seq` a

assist :: (IMonad m) => [a] -> c -> (a -> c -> m i i c) -> m i i c
assist [x] c f
  = f x c
assist (x:xs) c f
  = f x c >>= \c' -> assist xs c' f 

assist1 :: (IMonad m) => [a] -> (a -> m i i ()) -> m i i ()
assist1 [x] f
  = f x
assist1 (x:xs) f
  = f x >>= \c -> assist1 xs f

write n i a = inject @ArrayEffect (Write n i a) return
demandWrite n = inject @ArrayEffect (DemandWrite n) return

makeFunc ''ArrayEffect ''ArrayOperation

fork s = injectS @ArrayEffect Fork s
local s = injectS @ ArrayEffect Local s

type Bounds = (Int, Int)

unsafeCreateA = unsafeCreate @(Bounds, IO.IOArray Int Any)
unsafeUncoverA = unsafeUncover @(Bounds, IO.IOArray Int Any)
unsafeCreateB = unsafeCreate @(IO Any)
unsafeUncoverB = unsafeUncover @(IO Any)

runArrays
  :: (MemberAux (FindEffect Embed sig) Embed sig)
  => ITree (ArrayEffect :- sig) ('( '[], '[] ) :+ ps) (q :+ qs) a
  -> ITree sig ps qs a
runArrays = runArraysH

runArraysH
  :: (MemberAux (FindEffect Embed sig) Embed sig)
  => ITree (ArrayEffect :- sig) ('(p, w) :+ ps) (q :+ qs) a
  -> ITree sig ps qs a
runArraysH (Pure a) = return a
runArraysH (Impure (Oinl (Alloc i (a :: b))) c) 
  = do
      let upper = i - 1
      let bounds = (0, upper)
      arr <- injectIO (IO.newArray bounds a :: IO (IO.IOArray Int b))
      let arr' = (unsafeCoerce arr :: IO.IOArray Int Any)
      runArraysH (c (unsafeCreateA (bounds, arr')))
runArraysH (Impure (Oinl (Read n i)) c)
  = do
      let ((lower, upper), arr) = unsafeUncoverA n
      let offset = i + lower
      if offset > upper || offset < lower
        then error "Index out of bounds"
        else do 
          v <- injectIO (IO.readArray (arr :: IO.IOArray Int Any) offset)
          v `seq` runArraysH (c (unsafeCoerce v))
runArraysH (Impure (Oinl (Write n i (a :: b))) c)
  = do
      let ((lower, upper), arr) = unsafeUncoverA n
      let offset = i + lower
      if offset > upper || offset < lower
        then error "Index out of bounds"
        else do 
          v <- injectIO (IO.writeArray (unsafeCoerce arr :: IO.IOArray Int b) offset a) 
          v `seq` runArraysH (c ())
runArraysH (Impure (Oinl (DemandWrite n)) c)
  = runArraysH (c ())
runArraysH (Impure (Oinl (Length n)) c)
  = do
      let ((lower, upper), arr) = unsafeUncoverA n
      if upper - lower + 1 < 0
        then error "Should not be here"
        else runArraysH (c (upper - lower + 1))
runArraysH (Impure (Oinl (Join a b)) c)
  = runArraysH (c ())
runArraysH (Impure (Oinl (Wait (Phantom a))) c)
  = do 
      let t = unsafeUncoverB a
      v <- injectIO t
      v `seq` runArraysH (c $ unsafeCoerce v)
runArraysH (Impure (Oinl (Slice n i)) c)
  = do
      let ((lower, upper), arr) = unsafeUncoverA n
      let offset = i + lower
      if offset > upper || offset < lower
        then error ("Index out of bounds " ++ show i ++ " " ++ show (lower, upper))
        else do
          let n1 = (lower, offset)
          let n2 = (offset + 1, upper)
          runArraysH (c (unsafeCreateA (n1, arr), unsafeCreateA (n2, arr)))
runArraysH (Scope (Sinl Fork) s c)
  = do
      m <- injectFork (runArraysH (unsafeCoerce s)) 
      runArraysH (c (Phantom (unsafeCreateB m)))
runArraysH (Scope (Sinl Local) s c)
  = do
      m <- runArraysH (unsafeCoerce s)
      runArraysH (c m)
runArraysH (Impure (Oinr op) c) = Impure op (fmap (runArraysH) c)

example = runIO . runArrays $ do
  i <- alloc 100 3
  j <- alloc 15 False 
  (i1, i2) <- slice i 50 
  write j 0 True
  fork $ do
    v <- read j 3
    injectIO (print v)
    return () 
  write i1 0 17
  write i2 48 18
  join i1 i2
  k1 <- read i 0
  k2 <- read i 99
  injectIO (print (k1, k2))
  return "Hello"

example3 = runIO . runArrays $ do
  i <- alloc 100 4
  m <- fork $ do
    j <- alloc 100 13
    inner <- fork $ do
      k <- alloc 100 4
      read i 4
      read j 4
      read k 5
      return ()
    wait inner
    return 100
  hundred <- wait m
  write i 14 0
  return $ hundred + 1

example6 :: IO ()
example6 = runIO . runArrays $ do
  let length = 10000
  injectIO (putStrLn "Hello")
  arr <- alloc length 0
  write arr 0 10
  assist1 [0..(length - 1)] $ \i -> do
    j <- injectIO (getStdRandom (randomR @Int (1,100000)))
    write arr i j
  assist1 [0..(length - 1)] $ \i -> do
    j <- read arr i
    injectIO (putStrLn $ (show i) ++ ": " ++ (show j))
  injectIO (putStrLn "sorting...")
  example5 arr
  injectIO (putStrLn "end sorting...")
  assist1 [0..(length - 1)] $ \i -> do
    j <- read arr i
    injectIO (putStrLn $ (show i) ++ ": " ++ (show j))

{-example2 :: (Member ArrayEffect u a c i d, _) => ITree u c d String
example2 = do
  i <- alloc 100 3
  j <- read i 20
  write i 0 5
  return "hey"-}

{-assist1 [1..(len - 1)] $ \i -> do
      i_value <- read arr i
      end <- assist [(i - 1)..0] $ \j -> do
        j_value <- read arr j
        if j_value < i_value then do
          write arr (j + 1) i_value
          return False
        else do
          return True
      write arr (end + 1) i_value-}

partition :: (Member ArrayEffect u '(p, w) c i c{-, MemberAux (FindEffect Embed u) Embed u,
                      Lookup p n ~ '(r, '( 'X, 'X)), GetType r ~ Int-}, _) => Int -> ENat n -> ITree u c c Int
partition len arr = do
  let last = len - 1 -- c
  pivot <- read arr last
  i <- assist [0..(last - 1)] 0 $ \j i -> do
    j_value <- read arr j
    if j_value < pivot then do
      i_value <- read arr i
      write arr j i_value
      write arr i j_value
      return $ i + 1
    else
      return i
  i_value <- read arr i
  write arr i pivot
  write arr last i_value -- c
  return i

type Pred :: forall sig. HListEffect sig -> HList sig -> Nat -> ArrayIndex -> [Bool] -> ArrayResource -> Constraint
type Pred u d n p w r = 
  (Contains (FindEffect ArrayEffect u) '(p, w) d
  , Lookup p n ~ '(r, '(X, X))
  , MemberAux (FindEffect ArrayEffect u) ArrayEffect u
  , MemberAux (FindEffect Embed u) Embed u
  , GetType r ~ Int)

example5 :: (Ref c c, Pred u c n p w r{-Member ArrayEffect u a c i c, a ~ '(p, w), Lookup p n ~ '(r, '( 'X, X)),-}{-_-}) => ENat n -> ITree u c c ()
example5 arr = do
  len <- (length arr)
  if len <= 2 then do
    when (len == 2) $ do
      v0 <- read arr 0
      v1 <- read arr 1 
      when (v0 > v1) $ do
        write arr 0 v1
        write arr 1 v0
  else local $ do
    i <- partition len arr
    (i1, i2) <- slice arr (max (i - 1) 0)
    t <- fork $ do 
      demandWrite i1
      example5 i1
    example5 i2
    wait t
    join i1 i2
    return ()

{-example1 :: (Member ArrayEffect u a c i d, _) => ITree u c d String
example1 = do
  arr <- alloc 100 3
  write arr 0 5
  let pivot = 10
  assist [0..50] 0 $ \j i -> do
    j_value <- read arr j
    if j_value < pivot
      then do
        i_value <- read arr i
        write arr j i_value
        write arr i j_value
        return $ i + 1
      else
        return i
  return "hey"-}

  --k <- partition length arr
  --injectIO (putStrLn $ "partition point: " ++ show k)
  {-assist1 [0..(length - 1)] $ \i -> do
    j <- read arr i
    injectIO (putStrLn $ (show i) ++ ": " ++ (show j))-}
