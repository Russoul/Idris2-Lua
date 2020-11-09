module LuaGen

import Compiler.Common
import Compiler.CompileExpr

import Control.Monad.Syntax

import Core.Context
import Core.Directory

import Data.Bool.Extra
import Data.Buffer
import Data.List
import Data.List1
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Data.String.Extra
import Data.Strings
import Data.Vect

import Debug.Trace
import Idris.Driver

import System
import System.Clock
import System.File

import Utils.Hex
import Utils.Path

import LuaCommon
import OrderDefs
import LuaAst


data Stack : Type where
data Preamble : Type where
data LuaCode : Type where

logTopic : String
logTopic = "idris2-lua"

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
   debugOutput          : WithDefault Bool (Just False)  --DebugOutput
   omitEntryCall        : WithDefault Bool (Just False)  --OmitEntryCall
                    --omit 'require' statements in the header of the support script
                    --useful when you want to run idris in environment where not all libraries
                    --are supported or dynamic library loading is turned off
                    --as an example you can use Idris do develop for iOS or android using third party tools

--TODO local const table with integer indices of function values for faster calls
--TODO use <const> when targeting lua 5.4 ? (should enable declaration of 200+ local functions which is
--impossible for mutable local varibles (due to lua's own limitation)
--TODO use strings as backend for Int type in lua 5.1 and 5.2 as in these versions maximum integer precision is 52 bits
--even 48bits if you are to use Buffers


export
logLine :
     {auto opts : COpts}
   -> Lazy String
   -> Core ()
logLine str with (opts |> debugOutput |> get)
   logLine str | True = coreLift $ putStrLn ("[Debug] " ++ str)
   logLine str | False = pure ()

export
toMillis : Clock type -> Integer
toMillis (MkClock sec nan) =
   let scale = 1000 in
       scale * sec + (nan `div` 1000000)

export
showMillis : Integer -> String
showMillis n = show n ++ " ms"

%hide Core.TT.Visibility

stringifyVisibility : Visibility -> String
stringifyVisibility Global = ""
stringifyVisibility Local = "local"

|||As lua does not support general expressions with return values
|||We can emulate this with code blocks and local variables
|||Instead of returning a code block we assign its return value to a local variable
|||And pass both along the compilation pipeline
|||Code blocks build up until the pipeline reaches back any function definition
|||Stockpiled block then gets pasted into the body of that nearest containing function
LuaBlock : Type
LuaBlock = (LuaExpr {-Block (may be empty)-}, LuaExpr {-Expr representing the return value of that block-})

mkErrorAst : String -> LuaExpr
mkErrorAst str =
   LApp (LGVar (UN "error")) [LString str]

mkCrashAst : LuaExpr -> LuaExpr
mkCrashAst crash =
    LApp (LLambda [] (    LApp (LGVar (UN "print"))
                               [LPrimFn StrAppend [LString "ERROR: ", crash]]
                      <+> LApp (LGVar (UN "os.exit")) [LNumber "1"])) []

luaNull : LuaExpr
luaNull = LGVar (UN "null")

getArgsName : Name
getArgsName = UN "idris__getArgs"

stringifyNameGlobal : Name -> String
stringifyNameGlobal (NS ns n) = (show ns) ++ "." ++ stringifyNameGlobal n
stringifyNameGlobal (UN x) = x
stringifyNameGlobal (RF str) = "." ++ str
stringifyNameGlobal (MN x y) = "{" ++ x ++ ":" ++ show y ++ "}"
stringifyNameGlobal (PV n d) = "{P:" ++ stringifyNameGlobal n ++ ":" ++ show d ++ "}"
stringifyNameGlobal (DN _ n) = stringifyNameGlobal n
stringifyNameGlobal (Nested (outer, idx) inner)
    = show outer ++ ":" ++ show idx ++ ":" ++ stringifyNameGlobal inner
stringifyNameGlobal (CaseBlock outer i) = "case[" ++ show i ++ "]" ++ outer
stringifyNameGlobal (WithBlock outer i) = "with[" ++ show i ++ "]" ++ outer
stringifyNameGlobal (Resolved x) = "$resolved" ++ show x

stringifyNameMangle : Name -> String
stringifyNameMangle (NS ns n) = (validateIdentifier $ show ns) ++ "_" ++ stringifyNameMangle n
stringifyNameMangle (UN x) = validateIdentifier x
stringifyNameMangle (RF x) = "rf__" ++ x
stringifyNameMangle (MN x y) = "__" ++ (validateIdentifier x) ++ show y
stringifyNameMangle (PV n d) = "pat__" ++ stringifyNameMangle n ++ "_" ++ show d
stringifyNameMangle (DN _ n) = stringifyNameMangle n
stringifyNameMangle (Nested (outer, idx) inner)
    = "n__" ++ show outer ++ "_" ++ show idx ++ "_" ++ stringifyNameMangle inner
stringifyNameMangle (CaseBlock outer i) = "case__" ++ (validateIdentifier outer) ++ "_" ++ show i
stringifyNameMangle (WithBlock outer i) = "with__" ++ (validateIdentifier outer) ++ "_" ++ show i
stringifyNameMangle (Resolved x) = "res__" ++ show x


stringifyName : Visibility -> Name -> String
stringifyName Local name = stringifyNameMangle name
stringifyName Global name = "idris[" ++ show (stringifyNameGlobal name) ++ "]"

mutual
  stringifyBinOp : Nat -> String -> LuaExpr -> LuaExpr -> DeferredStr
  stringifyBinOp n op x y = [stringify n x
                            , " "
                            , op
                            , " "
                            ,stringify (S n) y]

  stringifyMethodApp : Nat -> String -> LuaExpr -> LuaExpr -> DeferredStr
  stringifyMethodApp n method x y = [stringify n x
                                    , ":", method
                                    , "("
                                    ,stringify (1 + n) y
                                    , ")"]

  stringifyFnApp :
     Nat
   -> (fn : String)
   -> Vect n LuaExpr
   -> DeferredStr
  stringifyFnApp n fn args =
    [ fn
    , "("
    ,sepBy (stringify (1 + n) <$> args |> toList) ", "
    , ""
    , ")"]

  --TODO add compiler option to throw when it encounters unsupported ops
  opNotSupportedErr : {auto copts : COpts} -> String -> String
  opNotSupportedErr op = "error(\"[Idris2] Operation not supported: '" ++ op ++ "'\")"

  stringifyBitOp : {auto copts : COpts}
     -> Nat
     -> PrimFn n
     -> Vect n LuaExpr
     -> LuaVersion
     -> DeferredStr
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
  stringifyBitOp n (ShiftL IntegerType) [x, y] ver
     = stringifyMethodApp n "shiftleft" x (LPrimFn (Cast IntegerType IntType) [y]) --bigint shifts are only implemented
                                                                                         --for 'Int' shift widths

  stringifyBitOp n (ShiftR IntegerType) [x, y] ver
     = stringifyMethodApp n "shiftright" x (LPrimFn (Cast IntegerType IntType) [y]) --bigint shifts are only implemented
                                                                                         --for 'Int' shift widths

  stringifyBitOp n (BAnd IntegerType) [x, y] ver = stringifyFnApp n "idris.bandbi" [x, y]
  stringifyBitOp n (BOr IntegerType) [x, y] ver = stringifyFnApp n "idris.borbi" [x, y]
  stringifyBitOp n (BXOr IntegerType) [x, y] ver = stringifyFnApp n "idris.bxorbi" [x, y]
  stringifyBitOp n op _ _ = [opNotSupportedErr (show op)]


  stringifyString : String -> String --this way we do not rely on specific escape patterns of the compiler backend
  stringifyString str =
    let vstr = show str in --unpack is necessary as function stack size is very limited in lua
        fromMaybe ("utf8.char(idris.unpack({" ++ join ", " (show . ord <$> unpack str) ++ "})) --[[ " ++ trimQuotes vstr ++ "--]]")
                  ((\str => fastAppend ["\"", str, "\""]) <$> escapeStringLua str) -- Try to escape simple ascii strings,
                                                                        -- otherwise fall back to `unpack`
                  -- TODO lua 5.3 supports unicode escape sequences, use them

  data AppPrec = Lower | Higher
  appPrec : LuaExpr -> AppPrec
  appPrec (LLVar x) = Higher
  appPrec (LGVar x) = Higher
  appPrec (LLambda xs x) = Lower
  appPrec (LApp x xs) = Higher
  appPrec (LPrimFn x xs) = Lower
  appPrec LTrue = Higher
  appPrec LFalse = Higher
  appPrec LNil = Higher
  appPrec (LNumber x) = Higher
  appPrec (LBigInt x) = Higher
  appPrec (LString x) = Higher
  appPrec (LTable xs) = Lower
  appPrec (LIndex x y) = Higher
  appPrec (LSeq x y) = Lower
  appPrec (LReturn x) = Lower
  appPrec (LAssign x y z) = Lower
  appPrec (LDeclVar x y) = Lower
  appPrec (LIfThenElse x y z) = Lower
  appPrec LBreak = Lower
  appPrec (LWhile x y) = Lower
  appPrec LDoNothing = Lower
  appPrec (LComment x) = Lower

  stringify :
        {auto copts : COpts}
     -> (n : Nat)
     -> LuaExpr
     -> DeferredStr
  stringify _ (LLVar name) =
    [stringifyName Local name]
  stringify _ (LGVar name) =
    [stringifyName Global name]
  stringify _ (LDeclVar Local name) =
    [stringifyVisibility Local, " ", stringifyName Local name]
  stringify n (LDeclVar Global name) =
    [stringifyVisibility Global, stringifyName Global name]
  stringify n (LLambda args body) =
    [ "function("
    , sepBy (pure . stringifyName Local <$> args) ", "
    , ")\n"
    , indent (S n)
    , stringify (S n) body , "\n"
    , indent n
    , "end" ]
  stringify n (LApp f xs) =
    case appPrec f of
      Lower =>
        [ "("
        , stringify n f
        , ")("
        , sepBy (stringify n <$> xs) ","
        , ")"]
      Higher =>
        [ stringify n f
        , "("
        , sepBy (stringify n <$> xs) ","
        , ")" ]
  stringify _ LNil = ["nil"]
  stringify _ LFalse = ["false"]
  stringify _ LTrue = ["true"]
  stringify _ (LNumber num) = [num]
  stringify _ (LBigInt num) = ["bigint:new(" , "\"" , num , "\"" , ")" ]
  stringify _ (LString s) = [stringifyString s]
  stringify _ (LComment s) = ["--[[ ",  s, " --]]"]
  stringify _ (LTable []) = ["{}"]
  stringify n (LTable kvs@(_ :: _)) =
    [ "{\n"
    , sepBy ((\(k, v) =>
            let general = [indent (1 + n), "[", stringify (1 + n) k, "]", " = \n", indent (2 + n), stringify (2 + n) v] in
                case k of
                     LDoNothing => [indent (1 + n), stringify (1 + n) v]
                     (LString str) => let chars = unpack str in
                        case ((\c => c == '_' || isAlpha c)
                              <$> chars |> head' `orElse` False)
                             && forAll (\x => isAlphaNum x || x == '_') chars of --TODO properly look into what lua allows here
                             True => [indent (1 + n), str, " = \n", indent (2 + n), stringify (2 + n) v]                           --lua can do
                             False => general
                     (LNumber num) => [indent (1 + n), show num, " = \n", indent (2 + n), stringify (2 + n) v]                     --better at optimising these
                     _ => general
            ) <$> kvs)
            ",\n"
    , "\n"
    , indent n
    , "}" ]
  stringify n (LIndex e i) =
    [ stringify n e
    , "["
    , the DeferredStr
       $ let general = stringify (1 + n) i in
          case i of
               (LString str) => let chars = unpack str in
                                    if ((\c => c == '_' || isAlpha c)
                                        <$> chars |> head' `orElse` False)
                                       && forAll (\x => isAlphaNum x || x == '_') chars
                                       then
                                          [show str]
                                       else
                                          general
               _ => general
    , "]" ]
  stringify n (LSeq x y) = [stringify n x , "\n" , indent n, stringify n y]
  stringify n (LReturn x) = ["return " , stringify (1 + n) x]
  stringify n (LAssign (Just vis) x y) =
    [ stringifyVisibility vis
    , if vis == Local then " " else ""
    , stringify n x
    , " = "
    , stringify n y
    ]
  stringify n (LAssign Nothing x y) =
    [stringify n x , " = " , stringify n y]
  stringify n (LIfThenElse cond x y) =
    [ "if "
    , stringify (1 + n) cond
    , " then\n"
    , indent (1 + n), stringify (1 + n) x , "\n"
    , indent n
    , "else\n"
    , indent (1 + n), stringify (1 + n) y
    , "\n"
    , indent n
    , "end" ]
  stringify _ LBreak = ["break"]
  stringify n (LWhile cond body) =
    [ "while "
    , stringify (1 + n) cond
    , " do\n"
    , indent (1 + n), stringify (1 + n) body
    , "\n"
    , indent n
    , "end" ]
  stringify _ LDoNothing = [""]
  stringify n (LPrimFn (Add ty) [x, y]) = stringifyBinOp n "+" x y
  stringify n (LPrimFn (Sub ty) [x, y]) = stringifyBinOp n "-" x y
  stringify n (LPrimFn (Mul ty) [x, y]) = stringifyBinOp n "*" x y
  stringify n (LPrimFn (Div IntType) [x, y]) with (copts |> luaVersion |> get >= Lua53)
     stringify n (LPrimFn (Div IntType) [x, y]) | True
       = stringifyBinOp n "//" x y
     stringify n (LPrimFn (Div IntType) [x, y]) | False
       = stringifyFnApp n "idris.div" [x, y]
  stringify n (LPrimFn (Div IntegerType) [x, y]) = stringifyBinOp n "/" x y
  stringify n (LPrimFn (Div DoubleType) [x, y]) = stringifyBinOp n "/" x y
  stringify n (LPrimFn (Mod ty) [x ,y]) = stringifyBinOp n "%" x y
  stringify n (LPrimFn (Neg ty) [x]) = ["- (", stringify n x, ")"]
  stringify n (LPrimFn op@(ShiftL _) args) = stringifyBitOp n op args (copts |> luaVersion |> get)
  stringify n (LPrimFn op@(ShiftR _) args) = stringifyBitOp n op args (copts |> luaVersion |> get)
  stringify n (LPrimFn op@(BAnd _) args)   = stringifyBitOp n op args (copts |> luaVersion |> get)
  stringify n (LPrimFn op@(BOr _) args)    = stringifyBitOp n op args (copts |> luaVersion |> get)
  stringify n (LPrimFn op@(BXOr _) args)   = stringifyBitOp n op args (copts |> luaVersion |> get)
  stringify n (LPrimFn (LT ty) [x, y]) = stringifyBinOp (S n) "<" x y
  stringify n (LPrimFn (LTE ty) [x, y]) = stringifyBinOp (S n) "<=" x y
  stringify n (LPrimFn (EQ ty) [x, y]) = stringifyBinOp (S n) "==" x y
  stringify n (LPrimFn (GTE ty) [x, y]) = stringifyBinOp (S n) ">=" x y
  stringify n (LPrimFn (GT ty) [x, y]) = stringifyBinOp (S n) ">" x y
  stringify n (LPrimFn StrLength [x]) = ["utf8.len(" , stringify (1 + n) x , ")"]
  stringify n (LPrimFn StrHead [x]) = ["utf8.sub(" , stringify (1 + n) x , ", 1, 1)"]
  stringify n (LPrimFn StrTail [x]) = ["utf8.sub(" , stringify (1 + n) x , ", 2)"]
  stringify n (LPrimFn StrIndex [str, i]) =
      let strI = stringify (1 + n) i in
         [ "utf8.sub("
         , stringify (1 + n) str
         , ", "
         , strI
         , ", "
         , strI
         , ")" ]
  stringify n (LPrimFn StrCons [x, xs]) =
    [ "("
    , stringify (1 + n) x
    , ") .. ("
    , stringify (1 + n) xs
    , ")" ]
  stringify n (LPrimFn StrAppend [x, xs]) =
    [ "(" , stringify (1 + n) x
    , ") .. ("
    , stringify (1 + n) xs
    , ")" ]
  stringify n (LPrimFn StrReverse [x]) = ["(" , stringify (1 + n) x , "):reverse()"]
  stringify n (LPrimFn StrSubstr [offset, len, str]) =
     let strOff = stringify (1 + n) offset in
        ["utf8.sub("
        , stringify (1 + n) str
        , ", "
        , strOff
        , ", "
        , strOff
        , " + ("
        , stringify (1 + n) len
        , ") - 1)" ]
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



  stringify n (LPrimFn (Cast StringType IntType) [x]) = stringifyFnApp n "idris.strtointeger" [x] --defined in support
  stringify n (LPrimFn (Cast StringType DoubleType) [x]) = stringifyFnApp n "tonumber" [x]
  stringify n (LPrimFn (Cast StringType IntegerType) [x]) = stringifyFnApp n "bigint:new" [x]


  stringify n (LPrimFn (Cast IntType CharType) [x]) = ["utf8.char(" , stringify (1 + n) x , ")"]
  stringify n (LPrimFn (Cast IntType DoubleType) [x]) = stringify n x
  stringify n (LPrimFn (Cast IntType IntegerType) [x]) = stringifyFnApp n "bigint:new" [x]


  stringify n (LPrimFn (Cast CharType IntegerType) [x]) = ["bigint:new(utf8.byte(" , stringify (1 + n) x , "))"]
  stringify n (LPrimFn (Cast CharType IntType) [x]) = ["utf8.byte(" , stringify (1 + n) x , ")"]


  stringify n (LPrimFn (Cast IntegerType DoubleType) [x]) = stringifyFnApp n "bigint.tonumber" [x]
  stringify n (LPrimFn (Cast IntegerType IntType) [x]) = stringifyFnApp n "bigint.tonumber" [x]
  stringify n (LPrimFn (Cast IntegerType StringType) [x]) = stringifyFnApp n "bigint.tostring" [x]


  stringify n (LPrimFn (Cast DoubleType IntType) [x]) = stringifyFnApp n "math.floor" [x]
  stringify n (LPrimFn (Cast DoubleType IntegerType) [x]) =
    ["bigint:new(math.floor(" , stringify (1 + n) x , "))" ]


  stringify n (LPrimFn (Cast ty StringType) [x]) = stringifyFnApp n "tostring" [x]
  stringify n (LPrimFn (Cast from to) [x]) =
    [ stringify n $ mkErrorAst $ "invalid cast: from " ++ show from ++ " to " ++ show to ]
  stringify n (LPrimFn BelieveMe [_, _, x]) = stringify n x
  stringify n (LPrimFn Crash [_, msg])
   = let ast = mkCrashAst msg in
         [stringify n ast]
  stringify n (LPrimFn op args) = stringify n $ mkErrorAst $ "unsupported primitive function: " ++ show op


record StackFrame where   --each function has its own table that represents its stackframe (function arguments not included)
  constructor MkStackFrame--each inner table has a unique (relative to all outer functions) name
  get : Int               --each table is indexed by consecutive integer values starting from 1 (because lua)
                          --each such value represents one local variable of the innermost function
                          --stack emulation is required to bypass lua's local variable limit which is capped at 200 per function
                          --table indexing is not as fast as register access but that is an unevitable trade-off
                          --and you can still theoretically blow 200 locals limitation calling function with excessive amount of arguments

                          --SO using this method: each function has stack size of 1 + number of arguments + number of let bindings
                          --actually each function has one extra local: '_ENV' but I don't think it counts towards the limit

record StackSt where
  constructor MkStackSt
  stack : List Int
  nextFrame : Int
  nextIndex  : Int --if stack is empty, points to the next free index in current thread

frameLowest : Int
frameLowest = 1

indexLowest : Int
indexLowest = 1

frameName : StackFrame -> Name
frameName (MkStackFrame i) = MN "frame" i

declFrameTable : StackFrame -> Int -> LuaExpr
declFrameTable frame numOfVars =
 if numOfVars > 0 then
       LAssign (Just Local) (LLVar (frameName frame)) (LTable (replicate (integerToNat (cast numOfVars)) (LDoNothing, LNil)))
    else
       LDoNothing

record PreambleSt where
  constructor MkPreambleSt
  preamble : SortedMap String String

pushFrame :
      {auto c : Ref Stack StackSt}
   -> Core StackFrame
pushFrame =
  do
    s <- get Stack
    let frame = nextFrame s
    let index = nextIndex s
    put Stack (record{ nextFrame $= (+1)
                     , nextIndex = indexLowest
                     , stack $= (index ::) } s)
    pure (MkStackFrame frame)

pushLocal :
      {auto c : Ref Stack StackSt}
   -> {auto frame : StackFrame}
   -> Core LuaExpr
pushLocal =
  do
    s <- get Stack
    let i = nextIndex s
    put Stack (record{nextIndex $= (+1)} s)
    pure (LIndex (LLVar (frameName frame)) (LNumber (show i)))

||| Returns the number of local variables in the popped frame
popFrame : {auto c : Ref Stack StackSt} -> Core Int
popFrame =
  do
     s <- get Stack
     let i = nextFrame s
     let v = nextIndex s
     case (i <= frameLowest, stack s) of
          (False, (nextIndex :: other)) => do
             put Stack (record{nextFrame $= (\i => i - 1), nextIndex = nextIndex, stack = other} s)
             pure (v - 1)
          (_, _) => throw (UserError "Attempt to pop from an empty stack")


popName : {auto c : Ref Stack StackSt} -> Core ()
popName =
  do
     s <- get Stack
     let i = nextIndex s
     if i <= indexLowest then
           throw (UserError "attempt to pop from an empty stack frame")
        else
           put Stack (record{nextIndex $= (\i => i - 1)} s)


getPreamble :
           {auto p : Ref Preamble PreambleSt}
        -> Core $ SortedMap String String
getPreamble = do
  x <- get Preamble
  pure x.preamble


addDefToPreamble :
           {auto preamble : Ref Preamble PreambleSt}
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
               throw $ InternalError $ "Attempt to redefine the preamble definition '" ++ name ++ "'"
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

justReturn : LuaExpr -> LuaBlock
justReturn expr = (LDoNothing, expr)

curriedApp : LuaExpr -> List LuaExpr -> LuaExpr
curriedApp head [] = head
curriedApp head (x :: xs) = curriedApp (LApp head [x]) xs

mkCaseImpl :
       {auto stack : Ref Stack StackSt}
    -> {auto frame : StackFrame}
    -> {auto opts : COpts}
    -> (retn : LuaExpr)
    -> (branches : List (LuaBlock {-condition-}, (LuaBlock) {-arm-}))
    -> (mbElse : Maybe LuaBlock)
    -> Core LuaExpr
mkCaseImpl retn (((blockA, cond), (blockB, arm)) :: xs) mbElse = do
  blockC <- mkCaseImpl retn xs mbElse
  let ifBranch = LIfThenElse cond (blockB <+> LAssign Nothing retn arm) blockC
  pure $ blockA <+> ifBranch
mkCaseImpl retn [] (Just (blockA, els)) =
  pure $ blockA <+> LAssign Nothing retn els
mkCaseImpl retn [] Nothing =
  pure $ mkErrorAst "Impossible else branch"


mkCase :
       {auto stack : Ref Stack StackSt}
    -> {auto frame : StackFrame}
    -> {auto opts : COpts}
    -> (branches : List (LuaBlock {-condition-}, (LuaBlock) {-arm-}))
    -> (mbElse : Maybe LuaBlock)
    -> Core LuaBlock
mkCase branches mbElse =
  do
    local <- pushLocal
    blockA <- mkCaseImpl local branches mbElse
    pure (blockA, local)

uninhabNS : Namespace
uninhabNS = preludeNS <.> mkNamespace "Uninhabited"

iorefNS : Namespace
iorefNS = mkNamespace "Data.IORef"

bufferNS : Namespace
bufferNS = mkNamespace "Data.Buffer"

stringsNS : Namespace
stringsNS = mkNamespace "Data.Strings"

strIterNS : Namespace
strIterNS = mkNamespace "Data.String.Iterator"

arrayNS : Namespace
arrayNS = mkNamespace "Data.IOArray.Prims"

systemNS : Namespace
systemNS = mkNamespace "System"

dirNS : Namespace
dirNS = mkNamespace "System.Directory"

infoNS : Namespace
infoNS = mkNamespace "System.Info"

fileNS : Namespace
fileNS = mkNamespace "System.File"

termNS : Namespace
termNS = mkNamespace "Utils.Term"

ioNS : Namespace
ioNS = preludeNS <.> mkNamespace "IO"

primioNS : Namespace
primioNS = mkNamespace "PrimIO"

extNames : List Name
extNames = [
             mkNamespacedName (Just iorefNS) "prim__newIORef"
           , mkNamespacedName (Just iorefNS) "prim__readIORef"
           , mkNamespacedName (Just iorefNS) "prim__writeIORef"
           , mkNamespacedName (Just arrayNS) "prim__newArray"
           , mkNamespacedName (Just arrayNS) "prim__arrayGet"
           , mkNamespacedName (Just arrayNS) "prim__arraySet"
           , mkNamespacedName (Just infoNS)  "prim__os"
           , mkNamespacedName (Just infoNS)  "prim__codegen"
           , mkNamespacedName (Just uninhabNS) "void"
           , mkNamespacedName (Just ioNS) "onCollect"
           , mkNamespacedName (Just ioNS) "onCollectAny"
           ]

foreignImpls : List Name
foreignImpls = [
                 ------------- Not Implemented -----------
                 mkNamespacedName (Just $ mkNamespace "Idris.IDEMode.REPL") "prim__fdopen"
               , mkNamespacedName (Just $ mkNamespace "Network.FFI") "prim__idrnet_accept"
               , mkNamespacedName (Just $ mkNamespace "Network.FFI") "prim__idrnet_bind"
               , mkNamespacedName (Just $ mkNamespace "Network.FFI") "prim__idrnet_create_sockaddr"
               , mkNamespacedName (Just $ mkNamespace "Network.FFI") "prim__idrnet_free"
               , mkNamespacedName (Just $ mkNamespace "Network.FFI") "prim__idrnet_sockaddr_family"
               , mkNamespacedName (Just $ mkNamespace "Network.FFI") "prim__idrnet_sockaddr_ipv4"
               , mkNamespacedName (Just $ mkNamespace "Network.FFI") "prim__idrnet_socket"
               , mkNamespacedName (Just $ mkNamespace "Network.FFI") "prim__socket_listen"

               , mkNamespacedName (Just $ mkNamespace "Network.Socket.Data") "prim__idrnet_af_inet"
               , mkNamespacedName (Just $ mkNamespace "Network.Socket.Data") "prim__idrnet_af_inet6"
               , mkNamespacedName (Just $ mkNamespace "Network.Socket.Data") "prim__idrnet_af_unix"
               , mkNamespacedName (Just $ mkNamespace "Network.Socket.Data") "prim__idrnet_af_unspec"
               , mkNamespacedName (Just $ mkNamespace "Network.Socket.Data") "prim__idrnet_errno"

               , mkNamespacedName (Just $ mkNamespace "System.Clock") "prim__clockTimeGcCpu"
               , mkNamespacedName (Just $ mkNamespace "System.Clock") "prim__clockTimeGcReal"
               , mkNamespacedName (Just $ mkNamespace "System.Clock") "prim__clockTimeMonotonic"
               , mkNamespacedName (Just $ mkNamespace "System.Clock") "prim__clockTimeProcess"
               , mkNamespacedName (Just $ mkNamespace "System.Clock") "prim__clockTimeThread"
               , mkNamespacedName (Just $ mkNamespace "System.Clock") "prim__clockTimeUtc"
               , mkNamespacedName (Just $ mkNamespace "System.Clock") "prim__osClockNanosecond"
               , mkNamespacedName (Just $ mkNamespace "System.Clock") "prim__osClockSecond"
               , mkNamespacedName (Just $ mkNamespace "System.Clock") "prim__osClockValid"

               , mkNamespacedName (Just ioNS) "prim__fork"
               , mkNamespacedName (Just systemNS) "prim__setEnv"
               , mkNamespacedName (Just systemNS) "prim__getEnvPair"
               , mkNamespacedName (Just systemNS) "prim__unsetEnv"
                 -------------------------------------------


               , mkNamespacedName (Just primioNS) "prim__nullAnyPtr"
               , mkNamespacedName (Just ioNS) "prim__putStr"
               , mkNamespacedName (Just ioNS) "prim__putChar"
               , mkNamespacedName (Just ioNS) "prim__getStr"
               , mkNamespacedName (Just ioNS) "prim__getChar"
               , mkNamespacedName (Just ioNS) "prim__getString"
               , mkNamespacedName (Just fileNS) "prim__flush"
               , mkNamespacedName (Just fileNS) "prim__writeLine"
               , mkNamespacedName (Just fileNS) "prim__readLine"
               , mkNamespacedName (Just fileNS) "prim__readChar"
               , mkNamespacedName (Just fileNS) "prim__readChars"
               , mkNamespacedName (Just fileNS) "prim__eof"
               , mkNamespacedName (Just fileNS) "prim__open"
               , mkNamespacedName (Just fileNS) "prim__close"
               , mkNamespacedName (Just fileNS) "prim__error"
               , mkNamespacedName (Just fileNS) "prim__fileErrno"
               , mkNamespacedName (Just fileNS) "prim__removeFile"
               , mkNamespacedName (Just fileNS) "prim__fileSize"
               , mkNamespacedName (Just fileNS) "prim__fPoll"
               , mkNamespacedName (Just fileNS) "prim__fileModifiedTime"
               , mkNamespacedName (Just fileNS) "prim__fileStatusTime"
               , mkNamespacedName (Just fileNS) "prim__stdin"
               , mkNamespacedName (Just fileNS) "prim__stdout"
               , mkNamespacedName (Just fileNS) "prim__stderr"
               , mkNamespacedName (Just fileNS) "prim__chmod"
               , mkNamespacedName (Just dirNS) "prim__changeDir"
               , mkNamespacedName (Just dirNS) "prim__currentDir"
               , mkNamespacedName (Just dirNS) "prim__createDir"
               , mkNamespacedName (Just dirNS) "prim__removeDir"
               , mkNamespacedName (Just dirNS) "prim__openDir"
               , mkNamespacedName (Just dirNS) "prim__closeDir"
               , mkNamespacedName (Just dirNS) "prim__dirEntry"
               , mkNamespacedName (Just dirNS) "prim__fileErrno"
               , mkNamespacedName (Just systemNS) "prim__getArgs"
               , mkNamespacedName (Just systemNS) "prim__getEnv"
               , mkNamespacedName (Just systemNS) "prim__exit"
               , mkNamespacedName (Just systemNS) "prim__system"
               , mkNamespacedName (Just stringsNS) "fastConcat"
               , mkNamespacedName (Just stringsNS) "fastUnpack"
               , mkNamespacedName (Just typesNS) "fastPack"
               , mkNamespacedName (Just termNS) "prim__setupTerm"
               , mkNamespacedName (Just termNS) "prim__getTermCols"
               , mkNamespacedName (Just termNS) "prim__getTermLines"
               , mkNamespacedName (Just bufferNS) "prim__newBuffer"
               , mkNamespacedName (Just bufferNS) "prim__bufferSize"
               , mkNamespacedName (Just bufferNS) "prim__setByte"
               , mkNamespacedName (Just bufferNS) "prim__getByte"
               , mkNamespacedName (Just bufferNS) "prim__setInt32"
               , mkNamespacedName (Just bufferNS) "prim__getInt32"
               , mkNamespacedName (Just bufferNS) "prim__setInt"
               , mkNamespacedName (Just bufferNS) "prim__getInt"
               , mkNamespacedName (Just bufferNS) "prim__setDouble"
               , mkNamespacedName (Just bufferNS) "prim__getDouble"
               , mkNamespacedName (Just bufferNS) "prim__setString"
               , mkNamespacedName (Just bufferNS) "prim__getstring"
               , mkNamespacedName (Just bufferNS) "prim__copyData"
               , mkNamespacedName (Just bufferNS) "prim__readBufferData"
               , mkNamespacedName (Just bufferNS) "prim__writeBufferData"
               , mkNamespacedName (Just bufferNS) "stringByteLength"
               , mkNamespacedName (Just strIterNS) "prim__fromString"
               , mkNamespacedName (Just strIterNS) "prim__uncons"
               ]

mutual -- TODO try remove in favour of forward declarions ?

  processCustomExtCall :
         {auto stack : Ref Stack StackSt}
      -> {auto frame : StackFrame}
      -> {auto opts : COpts}
      -> Name
      -> List NamedCExp
      -> Core LuaBlock
  processCustomExtCall name args
   = do (blocks, args) <- unzip <$> traverse processExpr args
        pure $ (concat blocks, curriedApp (LGVar $ name) args)


  --fully applied external name
  --Can be inlined ?? Because it *is* inlined at the moment !
  processExtCall :
         {auto stack : Ref Stack StackSt}
      -> {auto frame : StackFrame}
      -> {auto opts : COpts}
      -> Name
      -> List NamedCExp
      -> Core LuaBlock
  processExtCall name@(NS ns (UN n)) args =
    condC [
            ( pure $ ns == iorefNS
            ,
              case (n, args) of
                   ("prim__newIORef", [_, v, _]) =>
                      do (blockA, v) <- processExpr v
                         pure (blockA, LTable [(LString "val", v)])
                   ("prim__readIORef", [_, r, _]) =>
                      do
                        (blockA, r) <- processExpr r
                        pure (blockA, LIndex r (LString "val"))
                   ("prim__writeIORef", [_, r, v, _]) =>
                      do
                        (blockA, r) <- processExpr r
                        (blockB, v) <- processExpr v
                        pure (blockA <+> blockB <+> LAssign Nothing (LIndex r (LString "val")) v, LTable [(LString "tag", LString "0")] {-Unit-})
                   _ => processCustomExtCall name args )
            ,
            ( pure $ ns == arrayNS
            , case (n, args) of
                   ("prim__newArray", [_, len, init, _]) =>
                      do
                        (blockA, len) <- processExpr len
                        (blockB, init) <- processExpr init
                        table <- pushLocal
                        counter <- pushLocal
                        let loop = LWhile
                                 (LPrimFn (LTE IntType) [counter, len]) $
                                 (LAssign Nothing (LIndex table counter) init)
                                 <+> (LAssign Nothing counter (LPrimFn (Add IntType) [counter, LNumber "1"]))
                        pure (blockA <+> blockB <+> LAssign Nothing table (LTable [])
                              <+> LAssign Nothing counter (LNumber "1") <+> loop, table)
                   ("prim__arrayGet", [_, ar, i, _]) =>
                      do
                        (blockA, ar) <- processExpr ar
                        (blockB, i) <- processExpr i
                        pure (blockA <+> blockB, LIndex ar (LPrimFn (Add IntType) [i, LNumber "1"]))
                   ("prim__arraySet", [_, ar, i, v, _]) =>
                      do
                        (blockA, ar) <- processExpr ar
                        (blockB, i) <- processExpr i
                        (blockC, v) <- processExpr v
                        pure ( blockA
                                <+> blockB
                                <+> blockC
                                <+> LAssign Nothing
                                            (LIndex ar (LPrimFn (Add IntType) [i, LNumber "1"]))
                                            v
                             , LTable [(LString "tag", LString "0")] {-Unit-})
                   _ => processCustomExtCall name args )
             ,
             ( pure $ ns == infoNS
             , case n of
                    "prim__os" =>
                       do
                         args' <- traverse processExpr args
                         let (blockA, args) = unzip args'
                         pure (concat blockA, curriedApp (LGVar name) args) --defined in support file
                    _ => processCustomExtCall name args )
             ,
             ( pure $ ns == infoNS
             , case n of
                    "prim__codegen" =>
                       do
                         args' <- traverse processExpr args
                         let (blockA, args) = unzip args'
                         pure (concat blockA, curriedApp (LGVar name) args) --defined in support file
                    _ => processCustomExtCall name args )
             ,
             ( pure $ ns == uninhabNS
             , case n of
                    "void" =>
                       do
                         args' <- traverse processExpr args
                         let (blockA, args) = unzip args'
                         pure (concat blockA, curriedApp (LGVar name) args) --defined in support file
                    _ => processCustomExtCall name args )
             ,
             ( pure $ ns == ioNS
             , case n of
                    "prim__onCollectAny" =>
                       do
                         args' <- traverse processExpr args
                         let (blockA, args) = unzip args'
                         pure (concat blockA, curriedApp (LGVar name) args) --defined in support file
                    "prim__onCollect" =>
                       do
                         args' <- traverse processExpr args
                         let (blockA, args) = unzip args'
                         pure (concat blockA, curriedApp (LGVar name) args) --defined in support file
                    _ => processCustomExtCall name args) ] (processCustomExtCall name args)
  -- where
  --   notDefined : Core a
  --   notDefined          = throw $ InternalError $ "external primitive not implemented: " ++ show name
  processExtCall name args = processCustomExtCall name args





  readCCPart : String -> (String, String)
  readCCPart x =
    let (cc, def) = break (== ':') x
    in (cc, drop 1 def)

  processRequire : String -> (List (String, String))
  processRequire x = let names = split (== ',') x in
                         flip map (forget names) $
                           \name =>
                             let (h, t) = Strings.break (== '(') name in
                             case trim (drop 1 t) of
                                  "" => (trim h, trim h)
                                  t => (trim h, trim $ fst $ break (== ')') t)


  searchForeign' : List1 String -> Maybe (String, Maybe (List (String, String))) --def, require statements
  searchForeign' (x:::xs) =
    let (cc, def) = readCCPart x
    in  if cc == "lua"
        then
           let (def, req) = break (== '|') def in
               Just (def, if req == "" then Nothing else Just $ processRequire $ drop 1 req)
        else case xs of
                  (x :: xs) => searchForeign' (x ::: xs)
                  [] => Nothing

  -- If there is only one hint line, prefix 'lua:' can be skipped
  -- If there are multiple, find a line prefixed with 'lua:'
  searchForeign : List String -> Maybe (String, Maybe (List (String, String)))
  searchForeign [] = Nothing
  searchForeign (a :: b :: xs) = searchForeign' (a ::: (b :: xs))
  searchForeign [def] =
    let def = trim def
        def = if isPrefixOf "lua:" def then trim (strSubstr 4 (cast $ length def) def) else def
        (def, req) = break (== '|') def in
        Just (def, if req == "" then Nothing else Just $ processRequire $ drop 1 req)

  doCurryTransform : (def : String) -> (erased : List Nat) -> Maybe String
  doCurryTransform def erased =
    case split (toList1 "=>") (fastUnpack def) of
      argsAll ::: [body] =>
        let args = split (toList1 ",") argsAll
            trimmedArgs = (mapMaybe (filter (/= []) . Just . trim) $ forget args) in
          Just $ fastPack $ curryTransform (addErasedArgs trimmedArgs erased) (trim body)
      _ => Nothing
    where
      addErasedArgs : (args : List (List Char)) -> (erased : List Nat) -> List (List Char)
      addErasedArgs xs (0 :: is) = ['_'] :: addErasedArgs xs (map (`minus` 1) is)
      addErasedArgs (x :: xs) ((S i) :: is) = x :: addErasedArgs xs (i :: map (`minus` 1) is)
      addErasedArgs [] is = replicate (length is) ['_']
      addErasedArgs xs [] = xs

  preprocess : {auto defs : Ref Ctxt Defs} -> (foreignName : Name) -> (def : String) -> Core String
  preprocess name def = pure $ doCurryTransform def !(getErased name) `orElse` def

  processForeignDef :
          {auto defs : Ref Ctxt Defs}
       -> {auto opts : COpts}
       -> {auto preamble : Ref Preamble PreambleSt}
       -> Name
       -> List String
       -> List CFType
       -> CFType
       -> Core ()
  processForeignDef name hints argtys retty =
   case find (== name) foreignImpls of
        Just _ => pure () -- implemented internally
        Nothing =>
           do let ((def, maybeReq), replace)
                  = ((\x => (x, True)) <$> (searchForeign hints)) `orElse` ((stringifyName Global name, Nothing), False)
              def <- preprocess name def
              logLine $ "using %foreign " ++ def
              case maybeReq of
                   (Just packs) => do logLine $ "requiring " ++ (show $ map fst packs)
                                      traverse
                                        (\pack =>
                                          addDefToPreamble
                                           ("$" ++ snd pack)
                                            ((stringifyName Global (UN $ snd pack)) ++ " = require('" ++ fst pack ++ "')")
                                             True) -- its ok to require the same package multiple times, ignore all but first
                                        packs
                                                                              -- '$' makes sure all require statements
                                                                              -- appear above assignments that use them
                                      pure ()
                   Nothing => pure ()
              if replace then do
                    let strname = stringifyName Global name
                    addDefToPreamble strname (strname ++ " = " ++ def) False
                    pure ()
                 else
                    pure ()

  processPrimCmp :
         {auto stack : Ref Stack StackSt}
      -> {auto frame : StackFrame}
      -> {auto opts : COpts}
      -> PrimFn arity
      -> Vect arity NamedCExp
      -> Core LuaBlock
  processPrimCmp op args = do
      args' <- traverseVect processExpr args
      let (blockA, args) = unzip args'
      (blockB, cas) <- mkCase
                [(justReturn $ LPrimFn op args, justReturn (LNumber "1"))]
                (Just $ justReturn (LNumber "0"))
      pure (concat blockA <+> blockB, cas)

  constCaseIndex : NamedConstAlt -> LuaExpr -> Core LuaExpr
  constCaseIndex (MkNConstAlt const _) index =
     case constantTy const of
          (Just IntegerType) => pure $ LPrimFn (Cast IntegerType StringType) [index]
          (Just other) => pure index
          Nothing => throw $ UserError ("Cannot match on " ++ show const)

  processExpr :
            {auto stack : Ref Stack StackSt}
         -> {auto frame : StackFrame}
         -> {auto opts : COpts}
         -> NamedCExp
         -> Core LuaBlock
  processExpr (NmLocal _ n) = pure (LDoNothing, LLVar n)
  processExpr (NmRef _ n) = pure (LDoNothing, LGVar n)
  processExpr (NmLam _ n e) =
    do
      newFrame <- pushFrame
      (ce, e) <- processExpr {frame = newFrame} e
      vars <- popFrame
      pure (LDoNothing, LLambda [n] (declFrameTable newFrame vars <+> ce <+> LReturn e)) --paste inner block here
  processExpr (NmApp _ f args) =
    do
      (cf, f) <- processExpr f
      args <- traverse processExpr args
      let (cargs, args) = unzip args
      pure (cf <+> concat cargs, curriedApp f args)
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
      conVar <- pushLocal
      alts <- traverse (processConsAlt conVar) alts
      let table = LTable (replicate (alts |> length) (LDoNothing, LNil)) --preallocate space
      tableVar <- pushLocal
      let assignments = (\(k, v) => LAssign Nothing (LIndex tableVar k) v) <$> alts
      mdef <- sequenceMaybe $ processExpr <$> def
      let indexed = LIndex tableVar (LIndex conVar (LString "tag"))
      indexedVar <- pushLocal
      (blockB, cas) <- mkCase [(justReturn indexedVar, justReturn (LApp indexedVar []))] mdef
      pure (blockA
           <+> LAssign Nothing conVar sc
           <+> LAssign Nothing tableVar table
           <+> concat assignments
           <+> LAssign Nothing indexedVar indexed
           <+> blockB, cas)
  processExpr (NmConstCase _ sc rawalts def) =
    do
      (blockA, sc) <- processExpr sc
      constVar <- pushLocal
      alts <- traverse processConstAlt rawalts
      let table = LTable (replicate (alts |> length) (LDoNothing, LNil)) --preallocate space
      tableVar <- pushLocal
      let assignments = (\(k, v) => LAssign Nothing (LIndex tableVar k) v) <$> alts
      mdef <- sequenceMaybe $ processExpr <$> def
      index <-
          (\alt => constCaseIndex alt constVar)
          <$> head' rawalts `orElse` pure luaNull --orElse is in case there is only default branch of case clause
      let indexed = LIndex tableVar index
      indexedVar <- pushLocal
      (blockB, cas) <- mkCase [(justReturn indexedVar, justReturn (LApp indexedVar []))] mdef
      pure (blockA
           <+> LAssign Nothing constVar sc
           <+> LAssign Nothing tableVar table
           <+> concat assignments
           <+> LAssign Nothing indexedVar indexed
           <+> blockB, cas)
  processExpr (NmExtPrim _ p args) = do
     processExtCall p args
  processExpr (NmCon _ n mbtag args) =
    do
      args <- traverse processExpr args
      let (blockA, args) = unzip args
      tableVar <- pushLocal
      let conArgs = zipWith (\i, arg => (LString $ "arg" ++ (show i), arg)) [1..args |> length] args
      let mbName = if opts |> storeConstructorName |> get then [(LString "cons", LString $ stringifyName Global n), (LString "num", LNumber $ args |> length |> show)] else []
      let kvs = [(LString "tag", LString (processTag n mbtag))] ++ conArgs ++ mbName
      pure (concat blockA
           <+> LAssign Nothing tableVar (LTable [])
           <+> concat ((\(k, v) => LAssign Nothing (LIndex tableVar k) v) <$> kvs)
           , tableVar)
  processExpr (NmDelay _ t) =
    do
      newFrame <- pushFrame
      (blockA, t) <- processExpr {frame = newFrame} t
      vars <- popFrame
      pure (LDoNothing, LLambda [] (declFrameTable newFrame vars <+> blockA <+> LReturn t))
  processExpr (NmForce _ t) =
    do
      (blockA, t) <- processExpr t
      pure (blockA, LApp t [])
  processExpr (NmLet _ n val sc) =
    do
      (blockA, val) <- processExpr val
      (blockB, cs) <- processExpr sc
      pure (blockA <+> LAssign (Just Local) (LLVar n) val <+> blockB, cs) --TODO replace names, use stack
  processExpr (NmErased _) =
    pure (LDoNothing, LNil)
  processExpr (NmCrash _ msg) =
    pure (LDoNothing, mkErrorAst msg)

  --TODO copy-pasted(whole mutual block) from Compiler.Scheme.Common, PR export flag
  used : Name -> NamedCExp -> Bool
  usedCon : Name -> NamedConAlt -> Bool
  usedConst : Name -> NamedConstAlt -> Bool

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

  usedCon n (MkNConAlt _ _ _ sc) = used n sc

  usedConst n (MkNConstAlt _ sc) = used n sc

  processConsAlt :
        {auto stack : Ref Stack StackSt}
     -> {auto frame : StackFrame}
     -> {auto opts : COpts}
     -> (cons : LuaExpr)
     -> (alt : NamedConAlt)
     -> Core (LuaExpr {-tag-}, LuaExpr {-arm-})
  processConsAlt cons (MkNConAlt name mbtag args res') =
    do
      newFrame <- pushFrame
      (blockA, res) <- processExpr {frame = newFrame} res'
      let bindings =
       zipWith (\i, n => if used n res' then LAssign (Just Local) (LLVar n) $ LIndex cons (indexConstructorArg i) else LDoNothing)
                [1..args |> length] args --TODO use stack instread of let bindings, replace names
      vars <- popFrame
      pure (LString $ processTag name mbtag, LLambda [] $ declFrameTable newFrame vars
                                                          <+> concat bindings
                                                          <+> blockA {-blockA uses those bindings-}
                                                          <+> LReturn res)


  processConstAlt :
        {auto stack : Ref Stack StackSt}
     -> {auto frame : StackFrame}
     -> {auto opts : COpts}
     -> (alt : NamedConstAlt)
     -> Core (LuaExpr {-const-}, LuaExpr {-arm-})
  processConstAlt alt@(MkNConstAlt c res) =
    do
      const <- processConstant c
      let const =
          case c of
               (BI i) => LString (show i) --all constants are LString or LNumber
               _ => const
      newFrame <- pushFrame
      (blockA, res) <- processExpr {frame = newFrame} res
      vars <- popFrame
      pure (const, LLambda [] $ declFrameTable newFrame vars
                              <+> blockA
                              <+> LReturn res)


  indexConstructorArg : Nat -> LuaExpr
  indexConstructorArg i = LString $ "arg" ++ (show i)


  processTag : Name -> Maybe Int -> String
  processTag n Nothing = stringifyName Global n
  processTag _ (Just i) = show i

  getErased : {auto refs : Ref Ctxt Defs}
           -> Name
           -> Core (List Nat)
  getErased name =
    do Just def <- lookupCtxtExact name (gamma !(get Ctxt))
        | _ => throw (InternalError $ "[Lua] Could not find def: " ++ show !(toFullNames name))
       pure def.eraseArgs

  processDef :
           {auto c: Ref Stack StackSt}
        -> {auto opts : COpts}
        -> {auto refs : Ref Ctxt Defs}
        -> {auto preamble : Ref Preamble PreambleSt}
        -> (Name, NamedDef)
        -> Core LuaExpr {- returns an assignment expression (statement) -}
  processDef (n, MkNmFun args expr) =
   if (find (== n) extNames) |> isJust
      then
         pure LDoNothing --do not gen names for ext fns and foreign fns, done separately
      else do
         newFrame <- pushFrame
         (blockA, expr) <- processExpr {frame = newFrame} expr
         vars <- popFrame
         pure $ mkFnDecl n (reverse args) $ LApp (LLambda [] $ declFrameTable newFrame vars
                                <+> blockA
                                <+> LReturn expr) [] -- paste code block into the function body,
                                                     -- we have to wrap the code in a lambda and then immediately call it
                                                     -- to make sure the block & the return expr form a valid Lua expression
                                                     -- TODO don't do this if the body is already wrapped in at least one function
    where
      mkFnDecl : Name -> List Name -> LuaExpr -> LuaExpr
      mkFnDecl n [] expr = LAssign (Just Global) (LGVar n) expr
      mkFnDecl n (x :: xs) expr = mkFnDecl n xs (LLambda [x] (LReturn expr))


  processDef (n, MkNmError expr) =
    throw $ (InternalError (show expr))
  processDef (n, MkNmForeign hints argsty retty) = --those are added into the preamble
    do
      processForeignDef n hints argsty retty
      pure LDoNothing
  processDef (n, MkNmCon _ _ _) =
    pure LDoNothing  --we do not need to predefine structures in lua

getCOpts : Core COpts --TODO use directives ?
getCOpts =
   do
      opt1 <- coreLift $ getEnv "StoreConsName"
      opt2 <- coreLift $ getEnv "DynSupport"
      (Just opt3) <- coreLift $ do str <- getEnv "LuaVersion"
                                   pure (parseLuaVersion =<< str)
         | _ => throw (UserError "Could not parse Lua version from $LuaVersion, format: X.X[.X]")
      opt4 <- coreLift $ getEnv "NoRequire"
      opt5 <- coreLift $ getEnv "DebugOutput"
      opt6 <- coreLift $ getEnv "OmitEntryCall"
      pure $ MkCOptsInfo
               (thisOrDefault (opt1 >>= parseEnvBool))
               (thisOrDefault (opt2 >>= parseEnvBool))
               (MkWithDefault opt3 _)
               (thisOrDefault (opt4 >>= parseEnvBool))
               (thisOrDefault (opt5 >>= parseEnvBool))
               (thisOrDefault (opt6 >>= parseEnvBool))

translate : Ref Ctxt Defs -> ClosedTerm -> Core StrBuffer
translate defs term = do
  opts <- getCOpts

  clock0 <- coreLift $ clockTime Monotonic

  logLine "Lua compilation started [0/5]"
  logLine ("Using " ++ opts |> luaVersion |> get |> show)
  cdata <- getCompileData Cases term

  clock1 <- coreLift $ clockTime Monotonic

  logLine $ "Got compile data [1/5] in " ++ showMillis (toMillis $ timeDifference clock1 clock0)
  let ndefs = cdata.namedDefs
  let ctm = forget cdata.mainExpr

  clock2 <- coreLift $ clockTime Monotonic

  logLine $ "Looked up direct names [2/5] in " ++ showMillis (toMillis $ timeDifference clock2 clock1)
  let ndefs = (\(n, _, d) => (n, d)) <$> ndefs
  let ndefs = defsUsedByNamedCExp ctm (defsToUsedMap ndefs) -- work through relevant names only
  let ndefsMap = defsToUsedMap ndefs
  let ndefs = quicksort {defs = ndefsMap} ndefs -- sort names by dependency order
  s <- newRef Stack (MkStackSt [] frameLowest indexLowest)
  pr <- newRef Preamble (MkPreambleSt empty)
  cdefs <- traverse processDef ndefs

  clock3 <- coreLift $ clockTime Monotonic

  logLine $ "Compiled definitions [3/5] in " ++ showMillis (toMillis $ timeDifference clock3 clock2)
  let con_cdefs = concat cdefs
  --TODO tail call optimization
  frame <- pushFrame
  (block, main) <- processExpr {frame} ctm
  vars <- popFrame
  let frameTable = declFrameTable frame vars

  clock4 <- coreLift $ clockTime Monotonic

  logLine $ "Compiled main [4/5] in " ++ showMillis (toMillis $ timeDifference clock4 clock3)
  preamble <- getPreamble

  support <- if opts |> dynamicSupportLib |> get
             then
               pure "require(\"idris2-lua\")"
             else
               readDataFile $ "lua" </> "idris2-lua.lua"

  let returnPlan : DeferredStr =
             if opts |> omitEntryCall |> get
             then
               []
             else
               [
                 "\n--------- RETURN ---------\n"
               , stringify Z frameTable, "\n"
               , stringify Z block     , "\n"
               , stringify Z main
               ]

  let stringPlan : DeferredStr =
             [ " --------- SUPPORT DEFS ---------\n"
             , "idris = {}\n"
             , "idris.null = {}\n"
             , "local null = idris.null\n"
             , "idris.luaVersion = " ++ show (opts |> luaVersion |> get |> index) ++ "\n" --sets target Lua version to be used in support
             , "idris.noRequire  = " ++ (toLower . show) (opts |> noRequire |> get) ++ "\n"
             , support , "\n"
             , "local idris = idris\n"
             , "local W = idris.W\n"
             , "---------- PREAMBLE DEFS ----------\n"
             , join "\n" (preamble |> values)
             , "\n---------- CTX DEFS ----------\n"
             , stringify Z con_cdefs
             ]
          ++ returnPlan
          ++ ["\nreturn idris"]
  let mbyte = 1024 * 1024
  strbuf <- newRef LuaCode !(allocStrBuffer mbyte)
  traverse_ (writeStr LuaCode) stringPlan

  clock5 <- coreLift $ clockTime Monotonic

  logLine $ "Stringified lua [5/5] in " ++ showMillis (toMillis $ timeDifference clock5 clock4)
  logLine $ "All done in " ++ showMillis (toMillis $ timeDifference clock5 clock0)
  strbuf <- get LuaCode
  pure strbuf

bashScript : String -> String -> String
bashScript luaexe scriptname {-with extention-}
 =   "#!/usr/bin/env bash" ++ "\n"
  ++ "BASEDIR=$(dirname \"$0\")" ++ "\n"
  ++ luaexe ++ " $BASEDIR/" ++ scriptname ++ " $@"

getLuaExe : IO String
getLuaExe
 = do
      mbDefined <- getEnv "LuaExe"
      pure $ mbDefined `orElse` "lua"

build : Ref Ctxt Defs --TODO add option to build only the .lua file
     -> String
     -> ClosedTerm
     -> String {-relative-}
     -> Core String
build defs outputDir term file = do

  strbuf <- translate defs term
  let luaFile = file ++ ".lua"
  Right () <- coreLift $ writeBufferToFile (outputDir </> luaFile) strbuf.get strbuf.offset
   | Left err => do coreLift $ freeBuffer strbuf.get; throw $ FileErr (outputDir </> luaFile) err
  coreLift $ freeBuffer strbuf.get

  luaExe <- coreLift getLuaExe

  Right () <- coreLift $ writeFile (outputDir </> file) (bashScript luaExe luaFile)
   | Left err => do throw $ FileErr (outputDir </> file) err

  Right () <- coreLift $ chmodRaw (outputDir </> file) 0o755
   | Left err => do throw $ FileErr (outputDir </> file) err

  pure (outputDir </> file)

compile : Ref Ctxt Defs
       -> String
       -> String
       -> ClosedTerm
       -> String
       -> Core (Maybe String)
compile defs tmpDir outputDir term file = Just <$> build defs outputDir term file

execute : Ref Ctxt Defs -> String -> ClosedTerm -> Core ()
execute defs tmpDir term = do
  exe <- build defs tmpDir term "generated"
  coreLift $ fflush stdout
  coreLift $ system $ "'" ++ exe ++ "' "
  pure ()

luaCodegen : Codegen
luaCodegen = MkCG compile execute

export
main : IO ()
main = mainWithCodegens [("lua", luaCodegen)]
