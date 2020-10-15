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
data LuaExpr =  LLVar Name
              | LGVar Name --TODO add ability to index globals other than `idris`
              | LLambda (List Name) LuaExpr
              | LApp LuaExpr (List LuaExpr)
              | LPrimFn (PrimFn arity) (Vect arity LuaExpr)
              | LTrue          --literal 'true'
              | LFalse         --literal 'false'
              | LNil           --literal 'nil'
              | LNumber String --literal number
              | LBigInt String --literal bigint
              | LString String --literal string
              | LTable (List (LuaExpr, LuaExpr))
              | LIndex LuaExpr LuaExpr
              | LSeq LuaExpr LuaExpr
              | LFnDecl Name (List Name) LuaExpr --global function decl
              | LReturn LuaExpr
              | LAssign (Maybe Visibility) LuaExpr LuaExpr  --decl with initial val and reassignment
              | LDeclVar Visibility Name
              | LIfThenElse LuaExpr LuaExpr LuaExpr
              | LBreak
              | LWhile LuaExpr LuaExpr
              | LDoNothing
              | LComment String

public export
Semigroup LuaExpr where
  LDoNothing <+> y = y
  x <+> LDoNothing = x
  x <+> y = LSeq x y

public export
Monoid LuaExpr where
  neutral = LDoNothing

public export
primFnNames : List String
primFnNames =
   ["prim__cast_IntChar"
   ,"prim__cast_IntegerDouble"
   ,"prim__cast_IntDouble"
   ,"prim__cast_StringDouble"
   ,"prim__cast_DoubleInt"
   ,"prim__cast_CharInt"
   ,"prim__cast_IntegerInt"
   ,"prim__cast_StringInt"
   ,"prim__cast_DoubleInteger"
   ,"prim__cast_CharInteger"
   ,"prim__cast_IntInteger"
   ,"prim__cast_StringInteger"
   ,"prim__cast_DoubleString"
   ,"prim__cast_CharString"
   ,"prim__cast_IntegerString"
   ,"prim__cast_IntString"
   ,"prim__doubleCeiling"
   ,"prim__doubleFloor"
   ,"prim__doubleSqrt"
   ,"prim__doubleATan"
   ,"prim__doubleACos"
   ,"prim__doubleASin"
   ,"prim__doubleTan"
   ,"prim__doubleCos"
   ,"prim__doubleSin"
   ,"prim__doubleLog"
   ,"prim__doubleExp"
   ,"prim__crash"
   ,"prim__believe_me"
   ,"prim__strSubstr"
   ,"prim__strReverse"
   ,"prim__strAppend"
   ,"prim__strCons"
   ,"prim__strIndex"
   ,"prim__strTail"
   ,"prim__strHead"
   ,"prim__strLength"
   ,"prim__gt_String"
   ,"prim__gt_Double"
   ,"prim__gt_Char"
   ,"prim__gt_Integer"
   ,"prim__gt_Int"
   ,"prim__gte_String"
   ,"prim__gte_Double"
   ,"prim__gte_Char"
   ,"prim__gte_Integer"
   ,"prim__gte_Int"
   ,"prim__eq_String"
   ,"prim__eq_Double"
   ,"prim__eq_Char"
   ,"prim__eq_Integer"
   ,"prim__eq_Int"
   ,"prim__lte_String"
   ,"prim__lte_Double"
   ,"prim__lte_Char"
   ,"prim__lte_Integer"
   ,"prim__lte_Int"
   ,"prim__lt_String"
   ,"prim__lt_Double"
   ,"prim__lt_Char"
   ,"prim__lt_Integer"
   ,"prim__lt_Int"
   ,"prim__xor_Int"
   ,"prim__or_Integer"
   ,"prim__or_Int"
   ,"prim__and_Integer"
   ,"prim__and_Int"
   ,"prim__shr_Integer"
   ,"prim__shr_Int"
   ,"prim__shl_Integer"
   ,"prim__shl_Int"
   ,"prim__negate_Double"
   ,"prim__mod_Integer"
   ,"prim__mod_Int"
   ,"prim__div_Double"
   ,"prim__div_Integer"
   ,"prim__div_Int"
   ,"prim__mul_Double"
   ,"prim__mul_Integer"
   ,"prim__mul_Int"
   ,"prim__sub_Double"
   ,"prim__sub_Integer"
   ,"prim__sub_Int"
   ,"prim__add_Double"
   ,"prim__add_Integer"
   ,"prim__add_Int"
   ]


