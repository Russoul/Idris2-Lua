module LuaAst

import Core.Name
import Core.TT

import Data.Vect

%hide Core.TT.Visibility

public export
data Visibility = Local 
                | Global


export 
Eq Visibility where
 (==) Local Local = True
 (==) Global Global = True
 (==) _ _ = False


public export 
data LuaExpr = LVar Name
              | LLambda (List Name) LuaExpr
              | LApp LuaExpr (List LuaExpr)
              | LPrimFn (PrimFn arity) (Vect arity LuaExpr)
              | LTrue
              | LFalse
              | LNil
              | LNumber String
              | LBigInt String
              | LString String
              | LTable (List (Name, LuaExpr))
              | LIndex LuaExpr LuaExpr
              | LSeq LuaExpr LuaExpr
              | LFnDecl Visibility Name (List Name) LuaExpr
              | LReturn LuaExpr
              | LAssign (Maybe Visibility) LuaExpr LuaExpr  --decl with initial val and reassignment
              | LDeclVar Visibility Name
              | LIfThenElse LuaExpr LuaExpr LuaExpr 
              | LBreak
              | LWhile LuaExpr LuaExpr
              | LDoNothing

public export
Semigroup LuaExpr where
  LDoNothing <+> y = y
  x <+> LDoNothing = x
  x <+> y = LSeq x y

public export
Monoid LuaExpr where
  neutral = LDoNothing




