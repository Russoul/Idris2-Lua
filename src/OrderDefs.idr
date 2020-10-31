module OrderDefs

import Data.List
import Data.So
import Data.SortedMap
import Data.SortedSet
import Data.Vect

import Core.CompileExpr
import Core.FC
import Core.Name

import LuaCommon

-- Borrowed from the Node backend
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

usedNamesDef : NamedDef -> SortedSet Name
usedNamesDef (MkNmFun args exp) = usedNames exp
usedNamesDef (MkNmError exp) = usedNames exp
usedNamesDef (MkNmForeign cs args ret) = empty
usedNamesDef (MkNmCon _ _ _) = empty

defsToUsedMap : List (Name, NamedDef) -> SortedMap Name (SortedSet Name)
defsToUsedMap defs =
  fromList $ (\(n, d) => (n, usedNamesDef d)) <$> defs

calcUsed : SortedSet Name -> SortedMap Name (SortedSet Name) -> List Name -> SortedSet Name
calcUsed done d [] = done
calcUsed done d xs =
  let used_in_xs = foldl (\x, y => union x (fromMaybe empty y)) empty $ (\z => lookup z d) <$> xs
      new_done   = union done (fromList xs)
  in calcUsed (new_done) d (SortedSet.toList $ difference used_in_xs new_done)

calcUsedDefs : List Name -> List (Name, NamedDef) -> List (Name, NamedDef)
calcUsedDefs names defs =
  let usedNames = calcUsed empty (defsToUsedMap defs) names
  in List.filter (\(n, _) => contains n usedNames) defs

export
defsUsedByNamedCExp : NamedCExp -> List (Name, NamedDef) -> List (Name, NamedDef)
defsUsedByNamedCExp exp defs = calcUsedDefs (SortedSet.toList $ usedNames exp) defs

export
used : (Name, NamedDef) -> List (Name, NamedDef) -> SortedSet Name
used (n, _) defs = fromList $ map fst $ calcUsedDefs [n] defs

public export
interface MaybeRelated t r where
  mbRelated : (a : t) -> (b : t) -> Maybe (a `r` b)

contains : SortedSet a -> a -> Bool
contains = flip SortedSet.contains

%hide SortedSet.contains

-- `x` <= `y`: reflexive, transitive, antisymmetric (in x ~ y) relation. Forms a total order
-- forall x, y (x <= y) `xor` (Not $ x <= y)
public export
data Lte : (defs : List (Name, NamedDef)) -> (x : (Name, NamedDef)) -> (y : (Name, NamedDef)) -> Type where
  MkLte : {x, y, defs : _} ->
          let a = contains (used y defs) (fst x)
              b = contains (used x defs) (fst y)
          in  (0 prf : Either (So a, So $ not b) $ Either (So a, So b) (So $ not a, So $ not b))
           -> Lte defs x y

public export
{defs : _} -> MaybeRelated _ (Lte defs) where
  mbRelated x y
   = let
       a : Bool
       a = contains (used y defs) (fst x)
       b : Bool
       b = contains (used x defs) (fst y)
     in
       case (choose a, choose b) of
         (Left isA, Right notB) => Just $ MkLte (Left (isA, notB))
         (Left isA, Left isB) => Just $ MkLte (Right $ Left (isA, isB))
         (Right notA, Right notB) => Just $ MkLte (Right $ Right (notA, notB))
         _ => Nothing

-- The function type does not inforce the type requirements, r must be a total order
public export
quicksort : (mbRel : MaybeRelated a r) => List a -> List a
quicksort (y :: xs)
 = let (lte, gt) = partition (\x => isJust $ mbRelated {r} x y) xs in
    quicksort {r} lte ++ (y :: quicksort {r} gt)
quicksort [] = []
