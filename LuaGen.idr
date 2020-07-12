module LuaGen


import Core.Context
import Core.Directory
import Compiler.Common
import Compiler.CompileExpr
import Compiler.ES.RemoveUnused
import Idris.Driver
import Data.Vect
import Data.List
import System.File
import System
import Data.Strings
import Data.String.Extra as StrExtra
import Data.SortedMap
import Utils.Path
import Utils.Hex
import public LuaCommon
import public LuaAst

%hide Core.TT.Visibility

stringifyVisibility : Visibility -> String
stringifyVisibility Global = ""
stringifyVisibility Local = "local"

mkErrorAst : String -> LuaExpr
mkErrorAst str = 
    LApp (LVar (UN "error")) [LString str]
mkErrorAst' : LuaExpr -> LuaExpr
mkErrorAst' str = 
    LApp (LVar (UN "error")) [str]


ifThenElseName : Name
ifThenElseName = UN "idris__ifThenElse"

getArgsName : Name
getArgsName = UN "idris__getArgs"


stringifyName : Name -> String
stringifyName (NS ns n) = sepBy (validateIdentifier <$> reverse ns) "_" ++ "_" ++ stringifyName n
stringifyName (UN x) = validateIdentifier x
stringifyName (MN x y) = "__" ++ (validateIdentifier x) ++ show y
stringifyName (PV n d) = "pat__" ++ stringifyName n ++ "_" ++ show d
stringifyName (DN _ n) = stringifyName n
stringifyName (Nested (outer, idx) inner)
    = "n__" ++ show outer ++ "_" ++ show idx ++ "_" ++ stringifyName inner
stringifyName (CaseBlock outer i) = "case__" ++ (validateIdentifier outer) ++ "_" ++ show i
stringifyName (WithBlock outer i) = "with__" ++ (validateIdentifier outer)
stringifyName (Resolved x) = "res__" ++ show x


mutual
  stringifyBinOp : Nat -> (op : String) -> LuaExpr -> LuaExpr -> String
  stringifyBinOp n op x y = stringify n x ++ " " ++ op ++ "\n" 
                                              ++ stringify (S n) y
  stringifyFnApp : Nat -> (fn : String) -> Vect n LuaExpr -> String
  stringifyFnApp n fn args = 
    indent n ++ fn ++ "(\n" 
                  ++ sepBy' (stringify (S n) <$> args) ",\n" 
                  ++ "\n" ++ indent n ++ ")"
  
  stringify : (n : Nat) -> LuaExpr -> String
  stringify n (LVar name) = 
    indent n ++ stringifyName name
  stringify n (LDeclVar v name) = 
    indent n ++ stringifyVisibility v ++ (if v == Global then "" else " ") ++ stringifyName name  
  stringify n (LLambda args body) =
    indent n ++ "function(" ++ sepBy (stringifyName <$> args) ", " ++ ")\n"
                        ++ stringify (S n) body ++ "\n"
                        ++ indent n ++ "end"
  stringify n (LApp (LVar name) xs) =
     stringify n (LVar name) ++ "\n"
                  ++ indent n ++ "(\n" ++ sepBy (stringify (S n) <$> xs) ",\n" ++ "\n" ++ indent n ++ ")"

  stringify n (LApp f xs) = 
    indent n ++ "(\n" ++ stringify (S n) f ++ "\n" 
                  ++ indent n ++ ")(\n" ++ sepBy (stringify (S n) <$> xs) ",\n" ++ "\n" ++ indent n ++ ")"
  stringify n LNil = indent n ++ "nil"
  stringify n LFalse = indent n ++ "false"
  stringify n LTrue = indent n ++ "true"
  stringify n (LNumber num) = indent n ++ num
  stringify n (LBigInt num) = indent n ++ "bigint.new(" ++ "\"" ++ num ++ "\"" ++ ")"
  stringify n (LString s) = indent n ++ "\"" ++ escapeString s ++ "\""
  stringify n (LTable kvs) = 
        indent n ++ "{\n" 
                  ++ sepBy ((\(k, v) => indent (S n) ++ stringifyName k ++ " = \n" ++ stringify (n + 2) v) <$> kvs) ",\n" ++ "\n" ++ indent n ++ "}"
  stringify n (LIndex e i) = 
    indent n ++ "(\n" ++ stringify (S n) e 
     ++ ")\n" ++ indent n ++ "[\n" ++ stringify (S n) i ++ "\n" ++ indent n ++ "]"
  stringify n (LSeq x y) = stringify n x ++ "\n" ++ stringify n y
  stringify n (LFnDecl v name args body) = indent n ++ stringifyVisibility v
                  ++ (if v == Local then " " else "") ++ "function " ++ stringifyName name ++ "(" ++ sepBy (stringifyName <$> args) ", " ++ ")\n" 
                  ++ stringify (S n) body ++ "\n" ++ indent n ++ "end"
  stringify n (LReturn x) = indent n ++ "return \n" ++ stringify (S n) x ++ "\n" ++ indent n ++ ""
  stringify n (LAssign (Just vis) x y) = 
    indent n ++ stringifyVisibility vis ++ "\n" ++ stringify n x 
    ++ " =\n" ++ stringify (n + 2) y
  stringify n (LAssign Nothing x y) = 
    stringify n x ++ " =\n" ++ stringify (S n) y 
  stringify n (LIfThenElse cond x y) = 
    indent n ++ "if\n" ++ stringify (S n) cond ++ "\n" ++ indent n ++ "then\n" 
                  ++ stringify (S n) x ++ "\n"
                  ++ indent n ++ "else\n"
                  ++ stringify (S n) y ++ "\n" ++ indent n ++ "end"
  stringify n LBreak = indent n ++ "break"
  stringify n (LWhile cond body) = 
    indent n ++ "while\n" ++ stringify (S n) cond ++ "\n" ++ indent n ++ "do\n"
                  ++ stringify (S n) body ++ "\n" ++ indent n ++ "end"
  stringify n LDoNothing = ""
  stringify n (LPrimFn (Add ty) [x, y]) = stringifyBinOp n "+" x y
  stringify n (LPrimFn (Sub ty) [x, y]) = stringifyBinOp n "-" x y
  stringify n (LPrimFn (Mul ty) [x, y]) = stringifyBinOp n "*" x y
  stringify n (LPrimFn (Div IntType) [x, y]) = stringifyBinOp n "//" x y
  stringify n (LPrimFn (Div IntegerType) [x, y]) = stringifyFnApp n "idris__bigint_div" [x, y]
  stringify n (LPrimFn (Div DoubleType) [x, y]) = stringifyBinOp n "/" x y
  stringify n (LPrimFn (Mod ty) [x ,y]) = stringifyBinOp n "%" x y
  stringify n (LPrimFn (Neg ty) [x]) = indent n ++ "- (" ++ stringify Z x ++ ")"
  stringify n (LPrimFn (ShiftL ty) [x, y]) = stringifyBinOp n "<<" x y
  stringify n (LPrimFn (ShiftR ty) [x, y]) = stringifyBinOp n ">>" x y
  stringify n (LPrimFn (BAnd ty) [x, y]) = stringifyBinOp n "&" x y
  stringify n (LPrimFn (BOr ty) [x, y]) = stringifyBinOp n "|" x y
  stringify n (LPrimFn (BXOr ty) [x, y]) = stringifyBinOp n "~" x y
  stringify n (LPrimFn (LT IntegerType) [x, y]) = stringifyFnApp (S n) "bigint.compare" [x, y, (LString "<")] 
  stringify n (LPrimFn (LTE IntegerType) [x, y]) = stringifyFnApp (S n) "bigint.compare" [x, y, (LString "<=")]    
  stringify n (LPrimFn (EQ IntegerType) [x, y]) = stringifyFnApp (S n) "bigint.compare" [x, y, (LString "==")]    
  stringify n (LPrimFn (GTE IntegerType) [x, y]) = stringifyFnApp (S n) "bigint.compare" [x, y, (LString ">=")]    
  stringify n (LPrimFn (GT IntegerType) [x, y]) = stringifyFnApp (S n) "bigint.compare" [x, y, (LString ">")]    
  stringify n (LPrimFn (LT ty) [x, y]) = stringifyBinOp (S n) "<" x y     
  stringify n (LPrimFn (LTE ty) [x, y]) = stringifyBinOp (S n) "<=" x y  
  stringify n (LPrimFn (EQ ty) [x, y]) = stringifyBinOp (S n) "==" x y        
  stringify n (LPrimFn (GTE ty) [x, y]) = stringifyBinOp (S n) ">=" x y      
  stringify n (LPrimFn (GT ty) [x, y]) = stringifyBinOp (S n) ">" x y        
  stringify n (LPrimFn StrLength [x]) = indent n ++ "utf8.len(\n" ++ stringify (S n) x ++ ")"
  stringify n (LPrimFn StrHead [x]) = indent n ++ "utf8.sub(\n" ++ stringify (S n) x ++ ", 1, 1)"
  stringify n (LPrimFn StrTail [x]) = indent n ++ "utf8.sub(\n" ++ stringify (S n) x ++ ", 2)"
  stringify n (LPrimFn StrIndex [str, i]) = indent n ++ "utf8.sub(\n" ++ stringify (S n) str 
                  ++ ",\n" ++ stringify (S n) i ++ ",\n" 
                  ++ stringify (S n) i ++ ")" 
  stringify n (LPrimFn StrCons [x, xs]) =
    indent n ++ "(\n" ++ stringify (S n) x ++ ") .. (\n" 
                  ++ stringify (S n) xs ++ ")"
  stringify n (LPrimFn StrAppend [x, xs]) = 
    indent n ++ "(\n" ++ stringify (S n) x ++ ") .. (\n" 
                  ++ stringify (S n) xs ++ ")"
  stringify n (LPrimFn StrReverse [x]) = indent n ++ "(\n" ++ stringify (S n) x ++ "):reverse()"
  stringify n (LPrimFn StrSubstr [offset, len, str]) = 
    indent n ++ "utf8.sub(\n" ++ stringify (S n) str 
    ++ ",\n" ++ stringify (S n) offset 
    ++ ",\n" ++ stringify (S n) offset ++ " +\n" ++ stringify (S n) len ++ " - 1)"
  stringify n (LPrimFn DoubleExp args) = stringifyFnApp n "math.pow" args
  stringify n (LPrimFn DoubleLog args) = stringifyFnApp n "math.log" args
  stringify n (LPrimFn DoubleSin args) = stringifyFnApp n "math.sin" args
  stringify n (LPrimFn DoubleCos args) = stringifyFnApp n "math.cos" args
  stringify n (LPrimFn DoubleTan args) = stringifyFnApp n "math.tan" args
  stringify n (LPrimFn DoubleASin args) = stringifyFnApp n "math.asin" args
  stringify n (LPrimFn DoubleACos args) = stringifyFnApp n "math.acos" args
  stringify n (LPrimFn DoubleATan args) = stringifyFnApp n "math.atan" args
  stringify n (LPrimFn DoubleSqrt args) = stringifyFnApp n "math.sqrt" args
  stringify n (LPrimFn DoubleFloor args) = stringifyFnApp n "math.floor" args
  stringify n (LPrimFn DoubleCeiling args) = stringifyFnApp n "math.ceil" args



  stringify n (LPrimFn (Cast StringType IntType) [x]) = stringifyFnApp n "tonumber" [x] 
  stringify n (LPrimFn (Cast StringType DoubleType) [x]) = stringifyFnApp n "tonumber" [x]
  stringify n (LPrimFn (Cast StringType IntegerType) [x]) = stringifyFnApp n "bigint.new" [x]


  stringify n (LPrimFn (Cast IntType CharType) [x]) = indent n ++ "utf8.char(\n" ++ stringify (S n) x ++ ")"
  stringify n (LPrimFn (Cast IntType DoubleType) [x]) = stringify n x
  stringify n (LPrimFn (Cast IntType IntegerType) [x]) = stringifyFnApp n "bigint.new" [x]


  stringify n (LPrimFn (Cast CharType IntegerType) [x]) = indent n ++ "bigint.new(utf8.byte(\n" ++ stringify (S n) x ++ "))"
  stringify n (LPrimFn (Cast CharType IntType) [x]) = indent n ++ "utf8.byte(\n" ++ stringify (S n) x ++ ")"


  stringify n (LPrimFn (Cast IntegerType DoubleType) [x]) = stringifyFnApp n "bigint.unserialize" [x]
  stringify n (LPrimFn (Cast IntegerType IntType) [x]) = stringifyFnApp n "bigint.unserialize" [x]
  stringify n (LPrimFn (Cast IntegerType StringType) [x]) = indent n ++ "bigint.unserialize(\n" ++ stringify (S n) x ++ ", \"s\")"


  stringify n (LPrimFn (Cast DoubleType IntType) [x]) = stringifyFnApp n "math.floor" [x]
  stringify n (LPrimFn (Cast DoubleType IntegerType) [x]) = 
    stringifyFnApp n "math.floor" [ LApp (LIndex (LVar (UN "bigint")) (LVar (UN "unserialize"))) [x]]
  

  stringify n (LPrimFn (Cast ty StringType) [x]) = stringifyFnApp n "tostring" [x]
  stringify n (LPrimFn (Cast from to) [x]) = stringify n $ mkErrorAst $ "invalid cast: from " ++
                                                 show from ++ " to " ++ show to
  stringify n (LPrimFn BelieveMe [_, _, x]) = stringify n x
  stringify n (LPrimFn Crash [_, msg]) = stringify n $ mkErrorAst' msg 
  stringify n (LPrimFn op args) = stringify n $ mkErrorAst $ "unsupported primitive function: " ++ show op


replaceNames : List(Name, LuaExpr) -> LuaExpr -> LuaExpr
replaceNames names (LVar x) =
  case lookup x names of
       Nothing => LVar x
       Just e => e
replaceNames names (LDeclVar v n) = LDeclVar v n       
replaceNames names (LLambda args body) =
  LLambda args $ replaceNames names body
replaceNames names (LApp x args) = 
  LApp (replaceNames names x) (replaceNames names <$> args) 
replaceNames names (LPrimFn name args) = LPrimFn name (replaceNames names <$> args) 
replaceNames names LNil = LNil
replaceNames names LTrue = LTrue
replaceNames names LFalse = LFalse
replaceNames names (LNumber x) = LNumber x
replaceNames names (LString x) = LString x
replaceNames names (LBigInt x) = LBigInt x
replaceNames names (LIndex expr key) = LIndex (replaceNames names expr) (replaceNames names key)
replaceNames names (LTable ys) = 
  LTable (map (\(key, val) => (
                   key,
                   replaceNames names val)) ys)
replaceNames names (LSeq x y) = LSeq (replaceNames names x) (replaceNames names y)
replaceNames names (LFnDecl vis name args body) = LFnDecl vis name args (replaceNames names body)
replaceNames names (LReturn x) = LReturn (replaceNames names x)
replaceNames names (LAssign v x y) = LAssign v (replaceNames names x) (replaceNames names y)
replaceNames names (LIfThenElse cond tr fa) = 
  LIfThenElse (replaceNames names cond) (replaceNames names tr)
    (replaceNames names fa)
replaceNames names LBreak = LBreak
replaceNames names (LWhile cond body) = LWhile (replaceNames names cond) (replaceNames names body)
replaceNames names LDoNothing = LDoNothing


data NameGen : Type where
data Preamble : Type where

record NameGenSt where
  constructor MkNameGenSt
  nextName : Int

record PreambleSt where
  constructor MkPreambleSt
  preamble : SortedMap String String

genName : {auto c : Ref NameGen NameGenSt} -> Core Name
genName = 
  do
    s <- get NameGen
    let i = nextName s
    put NameGen (record{nextName $= (+1)} s)
    pure $ MN "idris__" i

getPreamble :
           {auto p : Ref Preamble PreambleSt}
        -> Core $ SortedMap String String
getPreamble = do
  x <- get Preamble
  pure x.preamble


addDefToPreamble : 
           {auto c : Ref NameGen NameGenSt}
        -> {auto preamble : Ref Preamble PreambleSt}
        -> String
        -> String
        -> Bool
        -> Core ()
addDefToPreamble name def okIfDefined = do
  do
    s <- getPreamble
    let dname = name
    case lookup dname s of
      Nothing =>
        do
          put Preamble (MkPreambleSt $ insert dname def s)
          pure ()
      Just _ => 
          if not okIfDefined then
               throw $ InternalError $ "Attempt to redefine preamble definition '" ++ name ++ "'"
             else
               pure ()


constantTy : Constant -> Maybe Constant
constantTy (I _)   = Just IntType
constantTy (BI _)  = Just IntegerType
constantTy (B8 _)  = Just Bits8Type
constantTy (B16 _) = Just Bits16Type
constantTy (B32 _) = Just Bits32Type
constantTy (B64 _) = Just Bits64Type
constantTy (Str _) = Just StringType
constantTy (Ch _)  = Just CharType
constantTy (Db _)  = Just DoubleType
constantTy _       = Nothing


processConstant : Constant -> Core LuaExpr 
processConstant (I x) = pure $ LNumber (show x)
processConstant (BI x) = pure $ LBigInt (show x)
processConstant (Str x) = pure $ LString x
processConstant (Ch x) = pure $ LString (Data.Strings.singleton x)
processConstant (Db x) = pure $ LNumber (show x)
processConstant WorldVal = pure $ LString (show WorldVal)
processConstant c = throw $ InternalError ("Unsupported constant '" ++ (show c) ++ "' detected")


mutual 

  processConsMatch : (cons : LuaExpr) 
              -> (alts : List LuaExpr {-var-}) 
              -> (maybeDefault : Maybe LuaExpr)
              -> Core LuaExpr
  processConsMatch cons (alt :: alts) md =
      let cond = LPrimFn (EQ StringType) [LIndex cons (LString "tag"), LIndex alt (LString "tag")] in
      pure $ LApp (LVar ifThenElseName) [
                  cond,
                  LIndex alt (LString "res"),                                        -- already a lambda
                  LLambda [] $ LReturn $ !(processConsMatch cons alts md)] 
  processConsMatch _ [] (Just def) = pure def
  processConsMatch _ [] Nothing = pure (mkErrorAst "no matching pattern")


  processConstMatch : (const : LuaExpr)
              -> (alts : List (LuaExpr, Constant))
              -> (maybeDefault : Maybe LuaExpr) 
              -> Core LuaExpr
  processConstMatch const ((alt, constant) :: alts) md =
    do
      let (Just constTy) = constantTy constant
        | Nothing => throw $ InternalError ("cannot match on " ++ (show constant))
      let cond = LPrimFn (EQ constTy) [const, LIndex alt (LString "const")] 
      pure $ LApp (LVar ifThenElseName) [
                        cond,
                        LIndex alt (LString "res"),                                  --already a lambda
                        LLambda [] $ LReturn $ !(processConstMatch const alts md)    
]
  processConstMatch _ [] (Just def) = pure def
  processConstMatch _ [] Nothing = pure (mkErrorAst "no matching constant")

  
  processPrimExt : {auto c : Ref NameGen NameGenSt}
            -> Name
            -> List NamedCExp
            -> Core LuaExpr
  processPrimExt (NS ["IORef", "Data"] (UN "prim__newIORef")) [_, v, _] =
    pure $ LTable [(UN "val", !(processExpr v))]
  processPrimExt (NS ["IORef", "Data"] (UN "prim__readIORef")) [_, r, _] =
    pure $ LIndex !(processExpr r) (LString "val")
  processPrimExt (NS ["IORef", "Data"] (UN "prim__writeIORef")) [_, r, v, _] = 
    pure $ LApp (LLambda [] $ LAssign Nothing (LIndex !(processExpr r) (LString "val")) !(processExpr v)) []
  processPrimExt (NS ["Prims", "IOArray", "Data"] (UN "prim__newArray")) [_, len, init, _] = 
    do
      len <- processExpr len
      init <- processExpr init
      let table = LVar (UN "arr")
      let counter = LVar (UN "i")
      let loop = LWhile  
               (LPrimFn (LTE IntType) [counter, len]) $
               (LAssign Nothing (LIndex table counter) init)
               <+> (LAssign Nothing counter (LPrimFn (Add IntType) [counter, LNumber "1"]))
      pure $ LApp (LLambda [] 
       (    LAssign (Just Local) table (LTable [])
        <+> LAssign (Just Local) counter (LNumber "1")
        <+> loop <+> LReturn table)) []        
  processPrimExt (NS ["Prims", "IOArray", "Data"] (UN "prim__arrayGet")) [_, ar, i, _] =
    do
      ar <- processExpr ar
      i <- processExpr i
      pure (LIndex ar (LPrimFn (Add IntType) [i, LNumber "1"] ))
  processPrimExt (NS ["Prims", "IOArray", "Data"] (UN "prim__arraySet")) [_, ar, i, v, _] = 
    do
      ar <- processExpr ar
      i <- processExpr i
      v <- processExpr v
      pure $ LApp (LLambda [] $ LAssign Nothing (LIndex ar (LPrimFn (Add IntType) [i, LNumber "1"])  ) v) []
  processPrimExt prim _ = throw $ InternalError $ "external primitive not implemented: " ++ show prim

   


  readCCPart : String -> (String, String)
  readCCPart x =
    let (cc, def) = break (== ':') x
    in (cc, drop 1 def)
  

  searchForeign : List String -> Maybe (String, Maybe String) --def, require
  searchForeign [] = Nothing
  searchForeign (x::xs) =
    let (cc, def) = readCCPart x
    in if cc == "lua" 
        then 
             let (def, req) = break (== '|') def in
                 Just (def, if req == "" then Nothing else Just $ drop 1 req)
        else searchForeign xs


  processForeign : 
             {auto refs : Ref Ctxt Defs} 
             -> {auto c : Ref NameGen NameGenSt}
             -> {auto preamble : Ref Preamble PreambleSt}
             -> Name
             -> List String
             -> List CFType
             -> CFType
             -> Core LuaExpr
  processForeign name@(NS ["Prelude"] (UN "prim__putStr")) hints argtys retty =
    do
       addDefToPreamble 
        ("$$" ++ show name)
         (stringify Z $ LFnDecl Global name [UN "x"] (LApp (LVar (UN "print")) [LVar (UN "x")]))
          False
       pure LDoNothing   
  processForeign name@(NS ["Prelude"] (UN "prim__getStr")) hints argtys retty =
    do
      addDefToPreamble ("$$" ++ show name) 
       (stringify Z $ LFnDecl Global name [] 
        (LReturn $ LApp (LIndex (LVar (UN "io")) (LString "read") )
         [])) False
      pure LDoNothing   
  processForeign name@(NS ["System"] (UN "prim__getArgs")) hints argtys retty =
    pure LDoNothing -- in support file
  processForeign name hints argtys retty = do
      let ((def, maybeReq), replace) 
          = ((\x => (x, True)) <$> (searchForeign hints)).orElse ((stringifyName name, Nothing), False)
      log 2 $ "using %foreign " ++ def
      case maybeReq of
           (Just pack) => do 
                         log 2 $ "requiring " ++ pack
                         addDefToPreamble 
                          ("$" ++ pack) 
                           ((stringifyName $ UN pack) ++ " = require('" ++ pack ++ "')")
                            True -- its ok to require the same package multiple times, ignore all but first

                                                             -- '$' makes sure all require statements
                                                             -- are above assingnments using them
           Nothing => pure ()
      
      if replace then do
            addDefToPreamble (show name) ((stringifyName name) ++ " = " ++ def) False
            pure LDoNothing 
         else
            pure LDoNothing

  processPrimCmp : {auto c : Ref NameGen NameGenSt} 
            -> PrimFn arity 
            -> Vect arity NamedCExp 
            -> Core LuaExpr
  processPrimCmp op args = do
      args <- traverseVect processExpr args
      pure $ LApp (LVar ifThenElseName) [
                      LPrimFn op args,
                      LLambda [] $ LReturn $ LNumber "1",
                      LLambda [] $ LReturn $ LNumber "0"]


  processExpr : {auto c : Ref NameGen NameGenSt} 
         -> NamedCExp -> Core LuaExpr
  processExpr (NmLocal _ n) = pure $ LVar n
  processExpr (NmRef _ n) = pure $ LVar n
  processExpr (NmLam _ n e) =
    pure $ LLambda [n] (LReturn !(processExpr e))
  processExpr (NmApp _ f args) =
    do
      cf <- processExpr f
      cargs <- traverse processExpr args
      pure $ LApp cf cargs
  processExpr (NmPrimVal _ c) = processConstant c
  processExpr (NmOp _ op@(EQ _) args) = processPrimCmp op args
  processExpr (NmOp _ op@(LT _) args) = processPrimCmp op args
  processExpr (NmOp _ op@(LTE _) args) = processPrimCmp op args
  processExpr (NmOp _ op@(GT _) args) = processPrimCmp op args
  processExpr (NmOp _ op@(GTE _) args) = processPrimCmp op args
  processExpr (NmOp _ StrIndex [str, i]) = 
    pure $ LPrimFn StrIndex [!(processExpr str), LPrimFn (Add IntType) [!(processExpr i), LNumber "1"]]
  processExpr (NmOp _ StrSubstr [offset, len, str]) = 
   pure $ LPrimFn StrSubstr [LPrimFn (Add IntType) [!(processExpr offset), LNumber "1"], !(processExpr len), !(processExpr str)]
  processExpr (NmOp _ op args) = 
    do
      args <- traverseVect processExpr args
      pure $ LPrimFn op args
  processExpr (NmConCase _ sc alts def) =
    do
      csc <- processExpr sc
      let conVar = !genName
      armVars <- traverse (\_ => genName) [1.. alts.length]
      calts <- traverse (\(alt, var) => processConsAlt conVar var alt) (zip alts armVars) 
      cdef <- lift $ processExpr <$> def
      --let cdef = (\def => LLambda [] (LReturn def)) <$> cdef_
      ifThenElse <- processConsMatch (LVar conVar) (LVar <$> armVars) cdef
      pure $ LApp (LLambda [] (LAssign (Just Local) (LVar conVar) csc
         <+> concat calts
         <+> LReturn ifThenElse)) []
  processExpr (NmConstCase _ sc alts def) = 
    do
      csc <- processExpr sc
      let constVar = !genName
      armVars <- traverse (\_ => genName) [1.. alts.length]
      calts1 <- traverse (\(alt, var) => processConstAlt var alt) (zip alts armVars)
      let (calts, consts) = unzip calts1
      cdef <- lift $ processExpr <$> def
      --let cdef = (\def => LLambda [] (LReturn def)) <$> cdef_
      ifThenElse <- processConstMatch (LVar constVar) (zip (LVar <$> armVars) consts) cdef
      pure $ LApp (LLambda [] (LAssign (Just Local) (LVar constVar) csc
          <+> concat calts
          <+> LReturn ifThenElse)) []
  processExpr (NmExtPrim _ p args) = processPrimExt p args
  processExpr (NmCon _ n tag args) =
    do
      cargs <- traverse processExpr args
      let tps = zipWith (\i, arg => (UN $ "t" ++ (show i), arg)) [1..(List.length cargs)] cargs
      pure $ LTable ([(UN "tag", LString (processTag n tag))] ++ tps)
  processExpr (NmDelay _ t) =
    do
      ct <- processExpr t
      pure $ LLambda [] (LReturn ct)
  processExpr (NmForce _ t) =
    do
      ct <- processExpr t
      pure $ LApp ct []
  processExpr (NmLet _ n val sc) =
    do
      cval <- processExpr val
      scs <- processExpr sc
      pure $ LApp (LLambda [] (LAssign (Just Local) (LVar n) cval <+> LReturn scs)) []
  processExpr (NmErased _) =
    pure LNil
  processExpr (NmCrash _ msg) =
    pure $ mkErrorAst msg


  processConsAlt : {auto c : Ref NameGen NameGenSt}
             -> Name
             -> Name
             -> (alt : NamedConAlt) 
             -> Core LuaExpr
  processConsAlt cons fresh (MkNConAlt name maybeTag args res) = 
    do
      cres <- processExpr res
      let nargs = args.length
      let bindings = zipWith (\i, n => (n, LIndex (LVar cons) (indexConstructorArg i))) [1..nargs] args

      pure $ LAssign (Just Local) (LVar fresh) $ LTable [(UN "tag", LString (processTag name maybeTag)),(UN "res", replaceNames bindings (LLambda [] (LReturn cres)))]


  processConstAlt : {auto c : Ref NameGen NameGenSt}
                -> Name
                -> (alt : NamedConstAlt)
                -> Core (LuaExpr, Constant)
  processConstAlt fresh (MkNConstAlt c res) =
    do
      cres <- processExpr res
      pure $ (LAssign (Just Local) (LVar fresh) $ LTable [(UN "const", !(processConstant c)), (UN "res", LLambda [] (LReturn cres))], c)


  indexConstructorArg : Nat -> LuaExpr
  indexConstructorArg i = LString $ "t" ++ (show i)


  processTag : Name -> Maybe Int -> String
  processTag n Nothing = show n
  processTag _ (Just i) = show i


  processDef : 
        {auto c: Ref NameGen NameGenSt} 
        -> {auto refs : Ref Ctxt Defs}
        -> {auto preamble : Ref Preamble PreambleSt}
        -> (Name, FC, NamedDef) 
        -> Core LuaExpr
  processDef (n, _, MkNmFun args expr) =
    do
      cexpr <- processExpr expr
      pure $ LFnDecl Global n args (LReturn cexpr)
  processDef (n, _, MkNmError expr) = 
    throw $ (InternalError (show expr))
  processDef (n, _, MkNmForeign hints argsty retty) = processForeign n hints argsty retty
  processDef (n, _, MkNmCon _ _ _) =
    pure LDoNothing


builtinSupportDefs : List LuaExpr -- add top level lua defs from here or through support library
builtinSupportDefs = []


translate : Ref Ctxt Defs -> ClosedTerm -> Core String
translate defs term = do
  cdata <- getCompileData Cases term
  let ndefs = cdata.namedDefs
  let ctm = forget cdata.mainExpr
  
  s <- newRef NameGen (MkNameGenSt 0)
  pr <- newRef Preamble (MkPreambleSt empty)
  log 5 $ "\n\n ---------- USED DEFS ---------\n" ++ sepBy (show <$> defsUsedByNamedCExp ctm ndefs) "\n\n"
  log 5 $ "\n\n ---------- MAIN -----------\n\n" ++ show ctm
  cdefs <- traverse processDef (defsUsedByNamedCExp ctm ndefs).reverse
  let con_cdefs = concat cdefs
  --TODO tail call optimization
  main <- processExpr ctm

  supportFile <- readDataFile $ "lua" </> "support-lua.lua"
  preamble <- getPreamble


  pure $        " --------- SUPPORT DEFS ---------\n" 
             ++ supportFile ++ "\n" 
             ++ stringify Z (concat builtinSupportDefs) 
             ++ "\n---------- PREAMBLE DEFS ----------\n"
             ++ sepBy preamble.values "\n" ++ "\n\n"
             ++ "\n---------- CTX DEFS ----------\n"
             ++ stringify Z con_cdefs
             ++ "\n--------- RETURN ---------\n" ++ stringify Z main



compile : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
        ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile defs tmpDir outputDir term file = do 
   
  res <- translate defs term

  (Right ()) <- coreLift $ writeFile (outputDir </> file) res
    | Left err => throw $ FileErr (outputDir </> file) err
    
  pure $ Just (outputDir </> file)

execute : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
execute defs tmpDir term = do
  res <- translate defs term
  let file = "generated.lua"
  (Right ())  <- coreLift $ writeFile (tmpDir </> file) res
     | Left err => throw $ FileErr (tmpDir </> file) err
  _ <- coreLift $ system $ "lua " ++ "\"" ++ escapeString (tmpDir </> file) ++ "\""
  pure ()

luaCodegen : Codegen
luaCodegen = MkCG compile execute


export
main : IO ()
main = mainWithCodegens [("lua", luaCodegen)]



