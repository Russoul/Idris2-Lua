module LuaGen



import Core.Context
import Core.Directory
import Compiler.Common
import Compiler.CompileExpr
import Compiler.ES.RemoveUnused
import Idris.Driver
import Data.Vect
import Data.List
import Data.Buffer
import System.File
import System
import Data.Bool.Extra
import Data.Strings
import Data.String.Extra as StrExtra
import Data.SortedMap
import Utils.Path
import Utils.Hex
import public LuaCommon
import public LuaAst


data WithDefault : (0 a : Type) -> Maybe a -> Type where
   MkWithDefault : {0 a : Type} -> (x : a) -> (mbdef : Maybe a) -> WithDefault a mbdef

namespace WithDefault
   export
   get : WithDefault a mba -> a
   get (MkWithDefault x _) = x

   export
   getDefault : {x : a} -> WithDefault a (Just x) -> a
   getDefault _ = x

   export
   thisOrDefault : {def : a} -> (Maybe a) -> WithDefault a (Just def)
   thisOrDefault (Just this) = MkWithDefault this _
   thisOrDefault Nothing = MkWithDefault def _

public export
record COpts where
   constructor MkCOptsInfo
   storeConstructorName : WithDefault Bool (Just False)  --StoreConsName
   dynamicSupportLib    : WithDefault Bool (Just True)   --DynSupport
   luaVersion           : WithDefault LuaVersion Nothing --LuaVersion
   noRequire            : WithDefault Bool (Just False)  --NoRequire
                    --omit 'require' statements in the header of the support script
                    --useful when you want to run idris in environment where not all libraries
                    --are supported or dynamic library loading is turned off
                    --as an example you can use Idris do develop for iOS or android using third party tools

--TODO local const table with integer indices of function values for faster calls
--TODO use <const> when targeting lua 5.4 ? (should enable declaration of 200+ local functions which is
--impossible for mutable local varibles (due to lua's own limitation)

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



--makes generated code ugly and unreadable but improves stringification speed A LOT
%hide LuaCommon.indent
%inline
indent : Nat -> String
indent n = ""

mutual
  stringifyBinOp : Nat -> String -> LuaExpr -> LuaExpr -> String
  stringifyBinOp n op x y = fastAppend [stringify n x
                                       , " ", op
                                       , "\n"
                                       , stringify (S n) y] 
  
  stringifyMethodApp : Nat -> String -> LuaExpr -> LuaExpr -> String
  stringifyMethodApp n method x y = fastAppend [stringify n x
                                               , ":", method
                                               , "(\n" 
                                               ,stringify (S n) y, ")"]
  stringifyFnApp : Nat -> (fn : String) -> Vect n LuaExpr -> String
  stringifyFnApp n fn args = 
    indent n ++ fn ++ "(\n" 
                  ++ sepBy' (stringify (S n) <$> args) ",\n" 
                  ++ "\n" ++ indent n ++ ")"
  
  --TODO add compiler option to throw when it encounters unsupported ops
  opNotSupportedErr : {auto copts : COpts} -> String -> String
  opNotSupportedErr op = "error(\"[Idris2] Operation not supported: '" ++ op ++ "'\")" 

  stringifyBitOp : {auto copts : COpts}
     -> Nat 
     -> PrimFn n 
     -> Vect n LuaExpr
     -> LuaVersion
     -> String
  stringifyBitOp n (ShiftL IntType) [x, y] ver with (ver >= Lua53) 
     stringifyBitOp n (ShiftL IntType) [x, y] ver | True = stringifyBinOp n "<<" x y
     stringifyBitOp n (ShiftL IntType) [x, y] ver | False = stringifyFnApp n "bit32.lshift" [x, y]
  stringifyBitOp n (ShiftR IntType) [x, y] ver with (ver >= Lua53) 
     stringifyBitOp n (ShiftR IntType) [x, y] ver | True = stringifyBinOp n ">>" x y
     stringifyBitOp n (ShiftR IntType) [x, y] ver | False = stringifyFnApp n "bit32.rshift" [x, y]
  stringifyBitOp n (BAnd IntType) [x, y] ver with (ver >= Lua53) 
     stringifyBitOp n (BAnd IntType) [x, y] ver | True = stringifyBinOp n "&" x y
     stringifyBitOp n (BAnd IntType) [x, y] ver | False = stringifyFnApp n "bit32.band" [x, y]
  stringifyBitOp n (BOr IntType) [x, y] ver with (ver >= Lua53) 
     stringifyBitOp n (BOr IntType) [x, y] ver | True = stringifyBinOp n "|" x y
     stringifyBitOp n (BOr IntType) [x, y] ver | False = stringifyFnApp n "bit32.bor" [x, y]
  stringifyBitOp n (BXOr IntType) [x, y] ver with (ver >= Lua53) 
     stringifyBitOp n (BXOr IntType) [x, y] ver | True = stringifyBinOp n "~" x y
     stringifyBitOp n (BXOr IntType) [x, y] ver | False = stringifyFnApp n "bit32.bxor" [x, y]
  stringifyBitOp n (ShiftL IntegerType) [x, y] ver = stringifyMethodApp n "shiftleft" x y 
  stringifyBitOp n (ShiftR IntegerType) [x, y] ver = stringifyMethodApp n "shiftright" x y 
  stringifyBitOp n op _ _ = opNotSupportedErr (show op)
  
  stringifyString : String -> String --this way we do not rely on specific escape patterns of the compiler backend
  stringifyString str = "utf8.char(" ++ sepBy (show . ord <$> unpack str) ", " ++ ") --[[ " ++ escapeString(str) ++ "--]]"

  --TODO this is slow, use mutable preallocated buffers
  stringify :
        {auto copts : COpts}
     -> (n : Nat) 
     -> LuaExpr 
     -> String
  stringify n (LVar name) = 
    indent n ++ stringifyName name
  stringify n (LDeclVar v name) = fastAppend 
    [ indent n, stringifyVisibility v, (if v == Global then "" else " "),  stringifyName name ]  
  stringify n (LLambda args body) = fastAppend
    [ indent n , "function(" , sepBy (stringifyName <$> args) ", " , ")\n"
    , stringify (S n) body , "\n"
    , indent n , "end" ]
  stringify n (LApp (LVar name) xs) = fastAppend
    [ stringify n (LVar name) , "(\n"
    , indent n , sepBy (stringify (S n) <$> xs) ",\n" , "\n" , indent n , ")" ]
  stringify n (LApp f xs) = fastAppend
    [ indent n , "(\n" , stringify (S n) f , ")(\n" 
    , indent n , sepBy (stringify (S n) <$> xs) ",\n" , "\n" , indent n , ")"]  
  stringify n LNil = indent n ++ "nil"
  stringify n LFalse = indent n ++ "false"
  stringify n LTrue = indent n ++ "true"
  stringify n (LNumber num) = indent n ++ num
  stringify n (LBigInt num) = fastAppend [ indent n , "bigint:new(" , "\"" , num , "\"" , ")" ]
  stringify n (LString s) = fastAppend [ indent n , stringifyString s ]
  stringify n (LTable kvs) = fastAppend
    [ indent n , "{\n" 
    , sepBy ((\(k, v) => fastAppend [indent (S n) , stringifyName k , " = \n" , stringify (n + 2) v]) <$> kvs) ",\n" , "\n" , indent n , "}" ]
  stringify n (LIndex (LVar name) i) = fastAppend
    [ indent n, stringifyName name , "\n[\n" , stringify (S n) i , "\n" , indent n , "]" ]
  stringify n (LIndex e i) = fastAppend
    [ indent n , "(\n" , stringify (S n) e 
    , ")\n" , indent n , "[\n" , stringify (S n) i , "\n" , indent n , "]" ]
  stringify n (LSeq x y) = fastAppend [ stringify n x , "\n" , stringify n y ]
  stringify n (LFnDecl v name args body) = fastAppend
    [ indent n , stringifyVisibility v
    , (if v == Local then " " else "") , "function " , stringifyName name , "(" , sepBy (stringifyName <$> args) ", " , ")\n" 
    , stringify (S n) body , "\n" , indent n , "end" ]
  stringify n (LReturn x) = fastAppend [ indent n , "return \n" , stringify (S n) x , "\n" , indent n , "" ]
  stringify n (LAssign (Just vis) x y) = fastAppend 
    [ indent n , stringifyVisibility vis , "\n" , stringify n x 
    , " =\n" , stringify (n + 2) y
    ]  
  stringify n (LAssign Nothing x y) = fastAppend
    [ stringify n x , " =\n" , stringify (S n) y ] 
  stringify n (LIfThenElse cond x y) = fastAppend
    [ indent n , "if\n" , stringify (S n) cond , "\n" , indent n , "then\n" 
    , stringify (S n) x , "\n"
    , indent n , "else\n"
    , stringify (S n) y , "\n" , indent n , "end" ]
  stringify n LBreak = indent n ++ "break"
  stringify n (LWhile cond body) = fastAppend
    [ indent n , "while\n" , stringify (S n) cond , "\n" , indent n , "do\n"
    , stringify (S n) body , "\n" , indent n , "end" ]
  stringify n LDoNothing = ""
  stringify n (LPrimFn (Add ty) [x, y]) = stringifyBinOp n "+" x y
  stringify n (LPrimFn (Sub ty) [x, y]) = stringifyBinOp n "-" x y
  stringify n (LPrimFn (Mul ty) [x, y]) = stringifyBinOp n "*" x y
  stringify n (LPrimFn (Div IntType) [x, y]) with (copts.luaVersion.get >= Lua53) 
     stringify n (LPrimFn (Div IntType) [x, y]) | True
       = stringifyBinOp n "//" x y
     stringify n (LPrimFn (Div IntType) [x, y]) | False 
       = stringifyFnApp n "idris__div" [x, y]
  stringify n (LPrimFn (Div IntegerType) [x, y]) = stringifyBinOp n "/" x y
  stringify n (LPrimFn (Div DoubleType) [x, y]) = stringifyBinOp n "/" x y
  stringify n (LPrimFn (Mod ty) [x ,y]) = stringifyBinOp n "%" x y
  stringify n (LPrimFn (Neg ty) [x]) = indent n ++ "- (" ++ stringify Z x ++ ")"
  stringify n (LPrimFn op@(ShiftL _) args) = stringifyBitOp n op args copts.luaVersion.get
  stringify n (LPrimFn op@(ShiftR _) args) = stringifyBitOp n op args copts.luaVersion.get
  stringify n (LPrimFn op@(BAnd _) args)   = stringifyBitOp n op args copts.luaVersion.get
  stringify n (LPrimFn op@(BOr _) args)    = stringifyBitOp n op args copts.luaVersion.get
  stringify n (LPrimFn op@(BXOr _) args)   = stringifyBitOp n op args copts.luaVersion.get
  stringify n (LPrimFn (LT ty) [x, y]) = stringifyBinOp (S n) "<" x y     
  stringify n (LPrimFn (LTE ty) [x, y]) = stringifyBinOp (S n) "<=" x y  
  stringify n (LPrimFn (EQ ty) [x, y]) = stringifyBinOp (S n) "==" x y        
  stringify n (LPrimFn (GTE ty) [x, y]) = stringifyBinOp (S n) ">=" x y      
  stringify n (LPrimFn (GT ty) [x, y]) = stringifyBinOp (S n) ">" x y        
  stringify n (LPrimFn StrLength [x]) = fastAppend [ indent n , "utf8.len(\n" , stringify (S n) x , ")" ]
  stringify n (LPrimFn StrHead [x]) = fastAppend [ indent n , "utf8.sub(\n" , stringify (S n) x , ", 1, 1)" ]
  stringify n (LPrimFn StrTail [x]) = fastAppend [ indent n , "utf8.sub(\n" , stringify (S n) x , ", 2)" ]
  stringify n (LPrimFn StrIndex [str, i]) = fastAppend
      let strI = stringify (S n) i in
         [ indent n , "utf8.sub(\n" , stringify (S n) str 
         , ",\n" , strI , ",\n" 
         , strI , ")" ] 
  stringify n (LPrimFn StrCons [x, xs]) = fastAppend
    [ indent n , "(\n" , stringify (S n) x , ") .. (\n" 
    , stringify (S n) xs , ")" ]
  stringify n (LPrimFn StrAppend [x, xs]) = fastAppend
    [ indent n , "(\n" , stringify (S n) x , ") .. (\n" 
    , stringify (S n) xs , ")" ]
  stringify n (LPrimFn StrReverse [x]) = fastAppend [ indent n , "(\n" , stringify (S n) x , "):reverse()" ]
  stringify n (LPrimFn StrSubstr [offset, len, str]) = fastAppend
     let strOff = stringify (S n) offset in
        [ indent n , "utf8.sub(\n" , stringify (S n) str 
        , ",\n" , strOff 
        , ",\n" , strOff , " +\n" , stringify (S n) len , " - 1)" ]
  stringify n (LPrimFn DoubleExp args) = stringifyFnApp n "math.pow" args
  stringify n (LPrimFn DoubleLog args) = stringifyFnApp n "math.log" args
  stringify n (LPrimFn DoubleSin args) = stringifyFnApp n "math.sin" args
  stringify n (LPrimFn DoubleCos args) = stringifyFnApp n "math.cos" args     --TODO create local bindings for math functions
  stringify n (LPrimFn DoubleTan args) = stringifyFnApp n "math.tan" args     -- for faster invokation
  stringify n (LPrimFn DoubleASin args) = stringifyFnApp n "math.asin" args
  stringify n (LPrimFn DoubleACos args) = stringifyFnApp n "math.acos" args
  stringify n (LPrimFn DoubleATan args) = stringifyFnApp n "math.atan" args
  stringify n (LPrimFn DoubleSqrt args) = stringifyFnApp n "math.sqrt" args
  stringify n (LPrimFn DoubleFloor args) = stringifyFnApp n "math.floor" args
  stringify n (LPrimFn DoubleCeiling args) = stringifyFnApp n "math.ceil" args



  stringify n (LPrimFn (Cast StringType IntType) [x]) = stringifyFnApp n "tonumber" [x] 
  stringify n (LPrimFn (Cast StringType DoubleType) [x]) = stringifyFnApp n "tonumber" [x]
  stringify n (LPrimFn (Cast StringType IntegerType) [x]) = stringifyFnApp n "bigint:new" [x]


  stringify n (LPrimFn (Cast IntType CharType) [x]) = fastAppend $ [ indent n , "utf8.char(\n" , stringify (S n) x , ")" ]
  stringify n (LPrimFn (Cast IntType DoubleType) [x]) = stringify n x
  stringify n (LPrimFn (Cast IntType IntegerType) [x]) = stringifyFnApp n "bigint:new" [x]


  stringify n (LPrimFn (Cast CharType IntegerType) [x]) = fastAppend [ indent n , "bigint:new(utf8.byte(\n" , stringify (S n) x , "))" ]
  stringify n (LPrimFn (Cast CharType IntType) [x]) = fastAppend [ indent n , "utf8.byte(\n" , stringify (S n) x , ")" ]


  stringify n (LPrimFn (Cast IntegerType DoubleType) [x]) = stringifyFnApp n "bigint.tonumber" [x]
  stringify n (LPrimFn (Cast IntegerType IntType) [x]) = stringifyFnApp n "bigint.tonumber" [x]
  stringify n (LPrimFn (Cast IntegerType StringType) [x]) = stringifyFnApp n "bigint.tostring" [x]


  stringify n (LPrimFn (Cast DoubleType IntType) [x]) = stringifyFnApp n "math.floor" [x]
  stringify n (LPrimFn (Cast DoubleType IntegerType) [x]) = fastAppend
    [ indent n , "bigint:new(math.floor(\n" , stringify (S n) x , "))" ]
  

  stringify n (LPrimFn (Cast ty StringType) [x]) = stringifyFnApp n "tostring" [x]
  stringify n (LPrimFn (Cast from to) [x]) = fastAppend 
    [ stringify n $ mkErrorAst $ "invalid cast: from "
    , show from , " to " , show to ]
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
replaceNames names (LAssign Nothing x y) = LAssign Nothing (replaceNames names x) (replaceNames names y) --assignment
replaceNames names (LAssign (Just v) x y) = LAssign (Just v) x (replaceNames names y) --declaration with initial value
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


|||As lua does not support general expressions with return values
|||We can emulate this with code blocks and local variables
|||Instead of returning a code block we assign its return value to a local variable
|||And pass both along the compilation pipeline
|||Code blocks build up until the pipeline reaches back any function definition
|||Stockpiled block then gets pasted into the body of that nearest containing function
LuaBlock : Type
LuaBlock = (LuaExpr {-Block (may be empty)-}, LuaExpr {-Expr representing the return value of that block-})

justReturn : LuaExpr -> LuaBlock
justReturn expr = (LDoNothing, expr)

mkCaseImpl : {auto ref : Ref NameGen NameGenSt}
    -> {auto opts : COpts}
    -> (retn : Name)
    -> (branches : List (LuaBlock {-condition-}, (LuaBlock) {-arm-}))
    -> (mbElse : Maybe LuaBlock)
    -> Core LuaExpr
mkCaseImpl retn (((blockA, cond), (blockB, arm)) :: xs) mbElse = do
  blockC <- mkCaseImpl retn xs mbElse
  let ifBranch = LIfThenElse cond (blockB <+> LAssign Nothing (LVar retn) arm) blockC
  pure $ blockA <+> ifBranch
mkCaseImpl retn [] (Just (blockA, els)) =
  pure $ blockA <+> LAssign Nothing (LVar retn) els
mkCaseImpl retn [] Nothing = 
  pure $ LAssign Nothing (LVar retn) LNil --retn is by default initialized to `nil`


mkCase : {auto ref : Ref NameGen NameGenSt}
    -> {auto opts : COpts}
    -> (branches : List (LuaBlock {-condition-}, (LuaBlock) {-arm-}))
    -> (mbElse : Maybe LuaBlock)
    -> Core LuaBlock
mkCase branches mbElse = 
  do
    name <- genName
    blockA <- mkCaseImpl name branches mbElse
    pure (LDeclVar Local name <+> blockA, LVar name)


mutual 


  extNames : List Name
  extNames = [NS ["IORef", "Data"] (UN "prim__newIORef")
             ,NS ["IORef", "Data"] (UN "prim__readIORef")
             ,NS ["IORef", "Data"] (UN "prim__writeIORef")
             ,NS ["Prims", "IOArray", "Data"] (UN "prim__newArray")
             ,NS ["Prims", "IOArray", "Data"] (UN "prim__arrayGet")
             ,NS ["Prims", "IOArray", "Data"] (UN "prim__arraySet")
             ,NS ["PrimIO"] (UN "prim__schemeCall")
             ,NS ["Info", "System"] (UN "prim__os")
             ,NS ["Uninhabited", "Prelude"] (UN "void")]

  --fully applied external name
  --can be inlined
  --THIS IS NOT A DEFINITION !
  processExtCall : 
            {auto c : Ref NameGen NameGenSt}
            -> {auto opts : COpts}
            -> Name
            -> List NamedCExp
            -> Core LuaBlock
  processExtCall (NS ["IORef", "Data"] (UN "prim__newIORef")) [_, v, _] =
    do
      (blockA, v) <- processExpr v
      pure (blockA, LTable [(UN "val", v)])
  processExtCall (NS ["IORef", "Data"] (UN "prim__readIORef")) [_, r, _] =
    do
      (blockA, r) <- processExpr r
      pure (blockA, LIndex r (LString "val"))
  processExtCall (NS ["IORef", "Data"] (UN "prim__writeIORef")) [_, r, v, _] = 
    do
      (blockA, r) <- processExpr r
      (blockB, v) <- processExpr v
      pure (blockA <+> blockB <+> LAssign Nothing (LIndex r (LString "val")) v, LTable [(UN "tag", LString "0")] {-Unit-})
  processExtCall (NS ["Prims", "IOArray", "Data"] (UN "prim__newArray")) [_, len, init, _] = 
    do
      (blockA, len) <- processExpr len
      (blockB, init) <- processExpr init
      arrname <- genName
      iname <- genName
      let table = LVar arrname
      let counter = LVar iname
      let loop = LWhile  
               (LPrimFn (LTE IntType) [counter, len]) $
               (LAssign Nothing (LIndex table counter) init)
               <+> (LAssign Nothing counter (LPrimFn (Add IntType) [counter, LNumber "1"]))
      pure (blockA <+> blockB <+> LAssign (Just Local) table (LTable []) 
            <+> LAssign (Just Local) counter (LNumber "1") <+> loop, table)  
  processExtCall (NS ["Prims", "IOArray", "Data"] (UN "prim__arrayGet")) [_, ar, i, _] =
    do
      (blockA, ar) <- processExpr ar
      (blockB, i) <- processExpr i
      pure (blockA <+> blockB, LIndex ar (LPrimFn (Add IntType) [i, LNumber "1"]))
  processExtCall (NS ["Prims", "IOArray", "Data"] (UN "prim__arraySet")) [_, ar, i, v, _] = 
    do
      (blockA, ar) <- processExpr ar
      (blockB, i) <- processExpr i
      (blockC, v) <- processExpr v
      pure (blockA <+> blockB <+> blockC <+> LAssign Nothing (LIndex ar (LPrimFn (Add IntType) [i, LNumber "1"])) v, LTable [(UN "tag", LString "0")] {-Unit-}) 
  processExtCall name@(NS ["PrimIO"] (UN "prim__schemeCall")) args = 
    do
      args' <- traverse processExpr args
      let (blockA, args) = unzip args'
      pure (concat blockA, LApp (LVar name) args) --defined in support file
  processExtCall name@(NS ["Info", "System"] (UN "prim__os")) args =
    do
      args' <- traverse processExpr args
      let (blockA, args) = unzip args'
      pure (concat blockA, LApp (LVar name) args) --defined in support file
  processExtCall name@(NS ["Uninhabited", "Prelude"] (UN "void")) args = 
    do
      args' <- traverse processExpr args
      let (blockA, args) = unzip args'
      pure (concat blockA, LApp (LVar name) args) --defined in support file
  processExtCall prim _ = throw $ InternalError $ "external primitive not implemented: " ++ show prim


   


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


  --Foreign definition
  --may be implemented as a function / binding 
  processForeignDef : 
             {auto refs : Ref Ctxt Defs} 
             -> {auto opts : COpts}
             -> {auto c : Ref NameGen NameGenSt}
             -> {auto preamble : Ref Preamble PreambleSt}
             -> Name
             -> List String
             -> List CFType
             -> CFType
             -> Core ()
  processForeignDef name@(NS ["Prelude"] (UN "prim__putStr")) hints argtys retty =
    pure ()   
  processForeignDef name@(NS ["Prelude"] (UN "prim__getStr")) hints argtys retty =
    pure ()   
  processForeignDef name@(NS ["System"] (UN "prim__getArgs")) hints argtys retty =
    pure () 
  processForeignDef name hints argtys retty = do
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
            pure () 
         else
            pure ()

  processPrimCmp : {auto c : Ref NameGen NameGenSt} 
            -> {auto opts : COpts}
            -> PrimFn arity 
            -> Vect arity NamedCExp 
            -> Core LuaBlock
  processPrimCmp op args = do
      args' <- traverseVect processExpr args
      let (blockA, args) = unzip args'
      (blockB, cas) <- mkCase 
                [(justReturn $ LPrimFn op args, justReturn $ LNumber "1")]
                (Just $ justReturn $ LNumber "0")
      pure (concat blockA <+> blockB, cas)          
                

  processExpr : {auto c : Ref NameGen NameGenSt} 
         -> {auto opts : COpts}
         -> NamedCExp
         -> Core LuaBlock
  processExpr (NmLocal _ n) = pure (LDoNothing, LVar n)
  processExpr (NmRef _ n) = pure (LDoNothing, LVar n)
  processExpr (NmLam _ n e) =
    do
      (ce, e) <- processExpr e 
      pure (LDoNothing, LLambda [n] (ce <+> LReturn e)) --paste inner block here
  processExpr (NmApp _ f args) =
    do
      (cf, f) <- processExpr f
      args <- traverse processExpr args
      let (cargs, args) = unzip args
      pure (cf <+> concat cargs, LApp f args)
  processExpr (NmPrimVal _ c) = pure (LDoNothing, !(processConstant c))
  processExpr (NmOp _ op@(EQ _) args) = processPrimCmp op args
  processExpr (NmOp _ op@(LT _) args) = processPrimCmp op args
  processExpr (NmOp _ op@(LTE _) args) = processPrimCmp op args
  processExpr (NmOp _ op@(GT _) args) = processPrimCmp op args
  processExpr (NmOp _ op@(GTE _) args) = processPrimCmp op args
  processExpr (NmOp _ StrIndex [str, i]) = do
    (blockA, str) <- processExpr str
    (blockB, i) <- processExpr i
    pure (blockA <+> blockB, LPrimFn StrIndex [str, LPrimFn (Add IntType) [i, LNumber "1"]])
  processExpr (NmOp _ StrSubstr [offset, len, str]) = 
    do
      (blockA, offset) <- processExpr offset
      (blockB, len) <- processExpr len
      (blockC, str) <- processExpr str
      pure (blockA <+> blockB <+> blockC, LPrimFn StrSubstr [LPrimFn (Add IntType) [offset, LNumber "1"], len, str])
  processExpr (NmOp _ op args) = 
    do
      args <- traverseVect processExpr args
      let (block, args) = unzip args 
      pure (concat block, LPrimFn op args)
  processExpr (NmConCase _ sc alts def) =
    do
      (blockA, sc) <- processExpr sc
      let conVar = !genName
      alts <- traverse (\alt => processConsAlt (LVar conVar) alt) alts 
      mdef <- lift $ processExpr <$> def
      (blockB, cas) <- mkCase alts mdef
      pure (blockA <+> LAssign (Just Local) (LVar conVar) sc <+> blockB, cas)   
  processExpr (NmConstCase _ sc alts def) = 
    do
      (blockA, sc) <- processExpr sc
      let constVar = !genName
      alts <- traverse (\alt => processConstAlt (LVar constVar) alt) alts
      mdef <- lift $ processExpr <$> def
      (blockB, cas) <- mkCase alts mdef
      pure (blockA <+> LAssign (Just Local) (LVar constVar) sc <+> blockB, cas)
  processExpr (NmExtPrim _ p args) = do
     --coreLift $ putStrLn $ "Ext call: " ++ stringifyName p ++ " with args " ++ show args
     processExtCall p args
  processExpr (NmCon _ n mbtag args) =
    do
      args <- traverse processExpr args
      let (blockA, args) = unzip args
      let conArgs = zipWith (\i, arg => (UN $ "arg" ++ (show i), arg)) [1..args.length] args
      let mbName = if opts.storeConstructorName.get then [(UN "name", LString $ show n), (UN "numArgs", LNumber $ show args.length)] else []
      pure (concat blockA, LTable ([(UN "tag", LString (processTag n mbtag))] ++ conArgs ++ mbName))
  processExpr (NmDelay _ t) =
    do
      (blockA, t) <- processExpr t
      pure (blockA, LLambda [] (LReturn t)) --no need to paste the block into lambda
  processExpr (NmForce _ t) =
    do
      (blockA, t) <- processExpr t
      pure (blockA, LApp t [])
  processExpr (NmLet _ n val sc) =
    do
      (blockA, val) <- processExpr val
      (blockB, cs) <- processExpr sc
      pure (blockA <+> LAssign (Just Local) (LVar n) val <+> blockB, cs) 
  processExpr (NmErased _) =
    pure (LDoNothing, LNil)
  processExpr (NmCrash _ msg) =
    pure (LDoNothing, mkErrorAst msg)

  mutual --TODO copy-pasted(whole mutual block) from Compiler.Scheme.Common, PR export flag
   used : Name -> NamedCExp -> Bool
   used n (NmLocal fc n') = n == n'
   used n (NmRef _ _) = False
   used n (NmLam _ _ sc) = used n sc
   used n (NmLet _ _ v sc) = used n v || used n sc
   used n (NmApp _ f args) = used n f || anyTrue (map (used n) args)
   used n (NmCon _ _ _ args) = anyTrue (map (used n) args)
   used n (NmOp _ _ args) = anyTrue (toList (map (used n) args))
   used n (NmExtPrim _ _ args) = anyTrue (map (used n) args)
   used n (NmForce _ t) = used n t
   used n (NmDelay _ t) = used n t
   used n (NmConCase _ sc alts def)
         = used n sc || anyTrue (map (usedCon n) alts)
               || maybe False (used n) def
   used n (NmConstCase _ sc alts def)
         = used n sc || anyTrue (map (usedConst n) alts)
               || maybe False (used n) def
   used n _ = False

   usedCon : Name -> NamedConAlt -> Bool
   usedCon n (MkNConAlt _ _ _ sc) = used n sc

   usedConst : Name -> NamedConstAlt -> Bool
   usedConst n (MkNConstAlt _ sc) = used n sc 

  processConsAlt : {auto c : Ref NameGen NameGenSt}
             -> {auto opts : COpts}
             -> (cons : LuaExpr)
             -> (alt : NamedConAlt) 
             -> Core (LuaBlock {-condition-}, LuaBlock {-arm-})
  processConsAlt cons (MkNConAlt name mbtag args res') = 
    do
      (blockA, res) <- processExpr res'
      -- let bindings = zipWith (\i, n => (n, LIndex cons (indexConstructorArg i))) [1..args.length] args
      let bindings = zipWith (\i, n => if used n res' then LAssign (Just Local) (LVar n) $ LIndex cons (indexConstructorArg i) else LDoNothing) [1..args.length] args
      let cond = LPrimFn (EQ StringType) [LIndex cons (LString "tag"), LString (processTag name mbtag)]
      pure (justReturn cond, (concat bindings <+> blockA {-blockA uses those bindings-}, res))


  processConstAlt : {auto c : Ref NameGen NameGenSt}
                -> {auto opts : COpts}
                -> (cons : LuaExpr)
                -> (alt : NamedConstAlt)
                -> Core (LuaBlock {-condition-}, LuaBlock {-arm-})
  processConstAlt cons (MkNConstAlt c res) =
    do
      let (Just constTy) = constantTy c
        | Nothing => throw $ InternalError ("cannot match on " ++ (show c))


      (blockA, res) <- processExpr res
      let cond = LPrimFn (EQ constTy) [cons, !(processConstant c)] 
      pure (justReturn cond, (blockA, res))


  indexConstructorArg : Nat -> LuaExpr
  indexConstructorArg i = LString $ "arg" ++ (show i)


  processTag : Name -> Maybe Int -> String
  processTag n Nothing = show n
  processTag _ (Just i) = show i

  --TODO skip primitive functions (arithmetic ops, str ops, etc..)
  -- as those never going to be applied normally
  processDef : 
        {auto c: Ref NameGen NameGenSt} 
        -> {auto opts : COpts}
        -> {auto refs : Ref Ctxt Defs}
        -> {auto preamble : Ref Preamble PreambleSt}
        -> (Name, FC, NamedDef) 
        -> Core LuaExpr {-block of code-}
  processDef (n, _, MkNmFun args expr) =
   if (find (== n) extNames) .isJust || (find (== show n) primFnNames) .isJust
      then
         pure LDoNothing --do not gen names for prim fns, ext fns and foreign fns, done separately
      else do   
         --coreLift $ putStrLn $ "def: " ++ stringifyName n
         (blockA, expr) <- processExpr expr
         pure $ LFnDecl Global n args $ blockA <+> (LReturn expr) --paste code block into function def
  processDef (n, _, MkNmError expr) = 
    throw $ (InternalError (show expr))
  processDef (n, _, MkNmForeign hints argsty retty) = --those are added into the preamble
    do
      --coreLift $ putStrLn $ "Foreign def: " ++ stringifyName n
      processForeignDef n hints argsty retty
      pure LDoNothing
  processDef (n, _, MkNmCon _ _ _) =
    pure LDoNothing  --we do not need to predefine structures in lua


builtinSupportDefs : List LuaExpr -- add top level lua defs from here or through support library
builtinSupportDefs = []


getCOpts : Core COpts
getCOpts = 
   do
      opt1 <- coreLift $ getEnv "StoreConsName"
      opt2 <- coreLift $ getEnv "DynSupport"
      (Just opt3) <- coreLift $ do str <- getEnv "LuaVersion"
                                   pure (parseLuaVersion <<= str)
         | _ => throw (UserError "Could not parse Lua version from $LuaVersion, format: X.X[.X]")
      opt4 <- coreLift $ getEnv "NoRequire"
      pure $ MkCOptsInfo 
               (thisOrDefault (opt1 >>= parseEnvBool)) 
               (thisOrDefault (opt2 >>= parseEnvBool)) 
               (MkWithDefault opt3 _) 
               (thisOrDefault (opt4 >>= parseEnvBool))


translate : Ref Ctxt Defs -> ClosedTerm -> Core String
translate defs term = do
  coreLift $ putStrLn "Lua compilation started [0/5]"
  opts <- getCOpts
  coreLift $ putStrLn ("Using " ++ show opts.luaVersion.get)
  cdata <- getCompileData Cases term
  coreLift $ putStrLn "Got compile data [1/5]"
  let ndefs = cdata.namedDefs
  let ctm = forget cdata.mainExpr
  coreLift $ putStrLn "Looked up direct names [2/5]"
  --let used = defsUsedByNamedCExp ctm ndefs 
  s <- newRef NameGen (MkNameGenSt 0)
  pr <- newRef Preamble (MkPreambleSt empty)
  cdefs <- traverse processDef ndefs.reverse
  coreLift $ putStrLn "Compiled definitions [3/5]"
  let con_cdefs = concat cdefs
  --TODO tail call optimization
  (block, main) <- processExpr ctm
  coreLift $ putStrLn "Compiled main [4/5]"
  preamble <- getPreamble

  support <- if opts.dynamicSupportLib.get
                   then
                     pure "require(\"idris2_lua\")"
                   else
                     readDataFile $ "lua" </> "idris2_lua.lua"


  let string = fastAppend
             [ " --------- SUPPORT DEFS ---------\n" 
             , "idris__luaVersion = " ++ show (index opts.luaVersion.get) ++ "\n" --sets target Lua version to be used in support
             , "idris__noRequire  = " ++ (toLower . show) opts.noRequire.get ++ "\n"
             , support , "\n" 
             , stringify Z (concat builtinSupportDefs) 
             , "\n---------- PREAMBLE DEFS ----------\n"
             , sepBy preamble.values "\n" , "\n\n"
             , "\n---------- CTX DEFS ----------\n"
             , stringify Z con_cdefs
             , "\n--------- RETURN ---------\n" 
             , stringify Z block
             , stringify Z main ]
  coreLift $ putStrLn "Stringified lua [5/5]"
  pure string


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
  lua <- coreLift $
    do
      mbDefined <- getEnv "LuaExe" 
      pure $ mbDefined `orElse` "lua"
  (Right ())  <- coreLift $ writeFile (tmpDir </> file) res
     | Left err => throw $ FileErr (tmpDir </> file) err
  _ <- coreLift $ system $ "'" ++ lua ++ "' " ++ "\"" ++ escapeString (tmpDir </> file) ++ "\""
  pure ()

luaCodegen : Codegen
luaCodegen = MkCG compile execute


export
main : IO ()
main = mainWithCodegens [("lua", luaCodegen)]



