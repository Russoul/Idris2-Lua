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
  ||| Returns all names referenced within the given expression.
  ||| Names are not chased down transitivily.
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

||| Returns all names referenced within the given definition.
||| Names are not chased down transitivily.
usedNamesDef : NamedDef -> SortedSet Name
usedNamesDef (MkNmFun args exp) = usedNames exp
usedNamesDef (MkNmError exp) = usedNames exp
usedNamesDef (MkNmForeign cs args ret) = empty
usedNamesDef (MkNmCon _ _ _) = empty

||| For each definition finds names referenced within it.
export
defsToUsedMap : List (Name, NamedDef) -> SortedMap Name (NamedDef, SortedSet Name)
defsToUsedMap defs =
  fromList $ (\(n, d) => (n, (d, usedNamesDef d))) <$> defs

||| The first argument is for local storage. Initialized with the empty set.
||| The second argument is a map from names to their dependencies.
||| The third argument is a set of names
||| Returns a set of names that the given names depend on.
calcUsed : SortedSet Name -> SortedMap Name (NamedDef, SortedSet Name) -> List Name -> SortedSet Name
calcUsed done d [] = done
calcUsed done d xs =
  let used_in_xs = foldl (\x, y => union x (fromMaybe empty (snd <$> y))) empty $ (\z => lookup z d) <$> xs
      new_done   = union done (fromList xs)
  in calcUsed (new_done) d (SortedSet.toList $ difference used_in_xs new_done)

calcUsedDefs : List Name -> SortedMap Name (NamedDef, SortedSet Name) -> List (Name, (NamedDef, SortedSet Name))
calcUsedDefs names usedMap =
  let usedNames = calcUsed empty usedMap names
  in List.filter (\(n, _) => contains n usedNames) (toList usedMap)

export
defsUsedByNamedCExp : NamedCExp -> SortedMap Name (NamedDef, SortedSet Name) -> List (Name, NamedDef)
defsUsedByNamedCExp exp usedMap = map (mapSnd fst) $ calcUsedDefs (SortedSet.toList $ usedNames exp) usedMap

export
used : (Name, NamedDef) -> SortedMap Name (NamedDef, SortedSet Name) -> SortedSet Name
used (n, _) usedMap = fromList $ map fst $ calcUsedDefs [n] usedMap

public export
interface MaybeRelated t r where
  mbRelated : (a : t) -> (b : t) -> Maybe (a `r` b)

contains : SortedSet a -> a -> Bool
contains = flip SortedSet.contains

%hide SortedSet.contains

-- `x` <= `y`: ?reflexive, transitive, antisymmetric relation. Forms a total order
public export
data Lte : (defs : SortedMap Name (NamedDef, SortedSet Name)) -> (x : (Name, NamedDef)) -> (y : (Name, NamedDef)) -> Type where
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

public export
quicksort : {defs : SortedMap Name (NamedDef, SortedSet Name)} -> List (Name, NamedDef) -> List (Name, NamedDef)
quicksort (y :: xs)
 = let (lte, gt) = partition (\x => isJust $ mbRelated {r = Lte defs} x y) xs in
    quicksort {defs} lte ++ (y :: quicksort {defs} gt)
quicksort [] = []
