module Linearity.Generator ( makeFunc ) where 

import Data.Char (toLower)
import Data.List ((\\), nub, sort)
import Data.Maybe (mapMaybe)
import Control.Monad (void, forM, replicateM)
import Language.Haskell.TH 
  (Name, Q, Dec(..), mkName, newName, nameBase, Clause, Body(..), Pat(..)
  , Clause(..), Exp(..), pprint, runQ, TyVarBndr(..), Type(..), report, lookupValueName)
import Language.Haskell.TH.Datatype (reifyDatatype, DatatypeInfo(..), ConstructorInfo(..), TypeSubstitution(..))

change :: Name -> Name
change name = mkName $ 
  case nameBase name of
    c:cs -> toLower c:filter (/= '\'') cs 

app :: Type -> Type -> Type
app t1 t2 = ArrowT `AppT` t1 `AppT` t2

getName :: TyVarBndr -> Name
getName (PlainTV a) = a
getName (KindedTV a _) = a

findToRemove :: [Type] -> [Name]
findToRemove = mapMaybe f
  where f (AppT (AppT EqualityT (VarT a)) _) = Just a
        f (AppT (AppT (ConT k) _) (VarT a))
          | nameBase k == "~" = Just a
        f _ = Nothing

makeFunc :: Name -> Name -> Q [Dec]
makeFunc other name = do
  info <- reifyDatatype name
  let cons = datatypeCons info
  let vars1 = datatypeVars info
  complete <- forM cons $ \con -> do
    let p = getName (vars1 !! 0)
    let q = getName (vars1 !! 1)
    let x = getName (vars1 !! 2)
    let fields = constructorFields con
    let con_name = constructorName con
    let changed_name = change con_name
    let vars2 = constructorVars con
    let ctx = constructorContext con
    let inj = mkName "inject"
    let ret = mkName "return"
    let mem = mkName "Member"
    let evolve = mkName "Evolve"
    let itree = mkName "ITree"
    u <- newName "u" 
    c <- newName "c" 
    d <- newName "d" 
    i <- newName "i" 
    v <- replicateM (length fields) (newName "x")
    let special = foldl1 AppT [ConT mem, ConT other, VarT u, VarT p, VarT c, VarT i, VarT d]
    let evolution = foldl1 AppT [ConT evolve, VarT c, VarT i, VarT q, VarT d]
    let ret_type = foldl1 AppT [ConT itree, VarT u, VarT c, VarT d, VarT x]
    let result = [ SigD changed_name (ForallT (vars1 ++ vars2 ++ [PlainTV u, PlainTV c, PlainTV i, PlainTV d]) (special:evolution:ctx) (foldr app ret_type fields)),
                    FunD changed_name [
                      Clause (map VarP v) (
                        NormalB (AppE (AppE (AppTypeE (AppTypeE (VarE inj) (ConT other)) (VarT q)) (foldl AppE (foldl AppTypeE (ConE con_name) (map (VarT) ([]))) (map VarE v))) (VarE ret))
                      ) []
                    ]
                  ]
    exists <- lookupValueName (nameBase changed_name)
    return $ case exists of
      Nothing -> result
      Just _ -> []
  return $ concat complete
