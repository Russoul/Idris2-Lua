module Order

import Decidable.Order

import Data.SortedSet
import Data.SortedMap
import Data.Vect
import Data.List
import Data.So

import Core.CompileExpr
import Core.Name
import Core.FC

mutual
  export
  usedNames : NamedCExp -> SortedSet Name
  usedNames (NmLocal fc n) = empty
  usedNames (NmRef fc n) = insert n empty
  usedNames (NmLam fc n e) = usedNames e
  usedNames (NmApp fc x args) = usedNames x `union` concat (usedNames <$> args)
  usedNames (NmPrimVal fc c) = empty
  usedNames (NmOp fc op args) = concat $ usedNames <$> args
  usedNames (NmConCase fc sc alts def) = (usedNames sc `union` concat (usedNamesConAlt <$> alts)) `union` maybe empty usedNames def
  usedNames (NmConstCase fc sc alts def) = (usedNames sc `union` concat (usedNamesConstAlt <$> alts)) `union` maybe empty usedNames def
  usedNames (NmExtPrim fc p args) = concat $ usedNames <$> args
  usedNames (NmCon fc x t args) = concat $ usedNames <$> args
  usedNames (NmDelay fc t) = usedNames t
  usedNames (NmForce fc t) = usedNames t
  usedNames (NmLet fc x val sc) = usedNames val `union` usedNames sc
  usedNames (NmErased fc) = empty
  usedNames (NmCrash fc msg) = empty

  usedNamesConAlt : NamedConAlt -> SortedSet Name
  usedNamesConAlt (MkNConAlt n t args exp) = usedNames exp

  usedNamesConstAlt : NamedConstAlt -> SortedSet Name
  usedNamesConstAlt (MkNConstAlt c exp) = usedNames exp

usedNamesDef' : NamedDef -> SortedSet Name
usedNamesDef' (MkNmFun args exp) = usedNames exp
usedNamesDef' (MkNmError exp) = usedNames exp
usedNamesDef' (MkNmForeign cs args ret) = empty
usedNamesDef' (MkNmCon _ _ _) = empty

export
usedNamesDef : (Name, NamedDef) -> SortedSet Name
usedNamesDef (n, d) = usedNamesDef' d `difference` (fromList [n])

public export
interface MaybeRelated t r where
  mbRelated : (a : t) -> (b : t) -> Maybe (a `r` b)

-- irreflexive, transitive, antisymmetric relation
-- `x` depends on `y`
public export
data DependsOn : (x : (Name, NamedDef)) -> (y : (Name, NamedDef)) -> Type where
  DoesDependOn : (0 prf0 : So $ contains (fst y) (usedNamesDef x))
              -> (0 prf1 : So $ not $ contains (fst x) (usedNamesDef y))
              -> DependsOn x y

public export
MaybeRelated _ DependsOn where
  mbRelated x y
   = case (choose $ contains (fst y) (usedNamesDef x), choose $ not $ contains (fst x) (usedNamesDef y)) of
       (Left yes0, Left yes1) => Just $ DoesDependOn yes0 yes1
       (_, _) => Nothing

public export
group : {n : _} -> List a -> Vect n (a -> Bool) -> Vect n (List a)
group [] _ = replicate _ []
group (x :: xs) fs =
  zipWith (++) (map (\f => fromMaybe [] (toMaybe (f x) [x])) fs) (group xs fs)

public export
quicksort : (mbRel : MaybeRelated a r) => List a -> List a
quicksort (x :: xs)
 = let p0 = (\e => isJust $ mbRelated {r} e x)
       p1 = (\e => isJust $ mbRelated {r} x e)
       [less, greater, other] = group xs [p0, p1, (\e => not (p0 e) && not (p1 e))]
    in less ++ (x :: other) ++ greater
quicksort [] = []
