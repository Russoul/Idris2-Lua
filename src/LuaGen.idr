module LuaGen

import Compiler.Common
import Compiler.CompileExpr
import Compiler.ES.RemoveUnused

import Control.Monad.Syntax

import Core.Context
import Core.Directory

import Data.Bool.Extra
import Data.Buffer
import Data.List
import Data.List1
import Data.SortedMap
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

import public LuaCommon
import public LuaAst


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

ifThenElseName : Name
ifThenElseName = UN "idris__ifThenElse"

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

--makes generated code ugly and unreadable but improves stringification speed A LOT
%hide LuaCommon.indent
%inline
indent : Nat -> String
indent n = ""

mutual
  stringifyBinOp : Nat -> String -> LuaExpr -> LuaExpr -> DeferedStr
  stringifyBinOp n op x y = [stringify n x
                            , " "
                            , op
                            , "\n"
                            ,stringify (S n) y]

  stringifyMethodApp : Nat -> String -> LuaExpr -> LuaExpr -> DeferedStr
  stringifyMethodApp n method x y = [stringify n x
                                    , ":", method
                                    , "(\n"
                                    ,stringify (S n) y
                                    , ")"]

  stringifyFnApp :
     Nat
   -> (fn : String)
   -> Vect n LuaExpr
   -> DeferedStr
  stringifyFnApp n fn args =
    [indent n
    , fn
    , "(\n"
    ,sepBy (stringify (S n) <$> args |> toList) ",\n"
    , "\n"
    , indent n , ")"]

  --TODO add compiler option to throw when it encounters unsupported ops
  opNotSupportedErr : {auto copts : COpts} -> String -> String
  opNotSupportedErr op = "error(\"[Idris2] Operation not supported: '" ++ op ++ "'\")"

  stringifyBitOp : {auto copts : COpts}
     -> Nat
     -> PrimFn n
     -> Vect n LuaExpr
     -> LuaVersion
     -> DeferedStr
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
        "utf8.char(idris.unpack({" ++ join ", " (show . ord <$> unpack str) ++ "})) --[[ " ++ trimQuotes vstr ++ "--]]"

  stringify :
        {auto copts : COpts}
     -> (n : Nat)
     -> LuaExpr
     -> DeferedStr
  stringify n (LLVar name) =
    [indent n, stringifyName Local name]
  stringify n (LGVar name) =
    [indent n, stringifyName Global name]
  stringify n (LDeclVar Local name) =
    [ indent n, stringifyVisibility Local, " ", stringifyName Local name]
  stringify n (LDeclVar Global name) =
    [ indent n, stringifyVisibility Global, stringifyName Global name]
  stringify n (LLambda args body) =
    [ indent n
    , "function("
    , sepBy (pure . stringifyName Local <$> args) ", "
    , ")\n"
    , (stringify (S n) body) , "\n"
    , indent n
    , "end" ]
  stringify n (LApp lvar@(LLVar name) xs) = --less noise
    [ (stringify n lvar)
    , "(\n"
    , indent n
    , sepBy (stringify (S n) <$> xs) ",\n"
    , "\n"
    , indent n
    , ")" ]
  stringify n (LApp gvar@(LGVar name) xs) = --less noise
    [ (stringify n gvar)
    , "(\n"
    , indent n
    , sepBy (stringify (S n) <$> xs) ",\n"
    , "\n"
    , indent n
    , ")" ]
  stringify n (LApp f xs) =                 --general case
    [ indent n , "(\n"
    , stringify (S n) f
    , ")(\n"
    , indent n
    , sepBy (stringify (S n) <$> xs) ",\n"
    , "\n" , indent n , ")"]
  stringify n LNil = [indent n, "nil"]
  stringify n LFalse = [indent n, "false"]
  stringify n LTrue = [indent n, "true"]
  stringify n (LNumber num) = [indent n, num]
  stringify n (LBigInt num) = [ indent n , "bigint:new(" , "\"" , num , "\"" , ")" ]
  stringify n (LString s) = [ indent n , stringifyString s ]
  stringify n (LComment s) = [ indent n, "--[[ ",  s, " --]]"]
  stringify n (LTable []) = ["{}"]
  stringify n (LTable kvs@(_ :: _)) =
    [ indent n , "{\n"
    , sepBy ((\(k, v) =>
            let general = [indent (S n), "[", stringify Z k, "]", " = \n", stringify (n + 2) v] in
                case k of
                     LDoNothing => [stringify (n + 1) v]
                     (LString str) => let chars = unpack str in
                        case ((\c => c == '_' || isAlpha c)
                              <$> chars |> head' `orElse` False)
                             && forAll (\x => isAlphaNum x || x == '_') chars of --TODO properly look into what lua allows here
                             True => [indent (S n), str, " = \n", stringify (n + 2) v]                           --lua can do
                             False => general
                     (LNumber num) => [indent (S n), show num, " = \n", stringify (n + 2) v]                     --better at optimising these
                     _ => general
            ) <$> kvs)
            ",\n"
    , "\n"
    , indent n
    , "}" ]
  stringify n (LIndex e i) =
    [ indent n
    , "\n"
    , stringify (S n) e
    , "\n"
    , indent n
    , "[\n"
    , the DeferedStr
       $ let general = stringify (S n) i in
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
    , "\n"
    , indent n
    , "]" ]
  stringify n (LSeq x y) = [ stringify n x , "\n" , stringify n y ]
  stringify n (LFnDecl name args body) =
    [ indent n
    , stringifyName Global name
    , " = "
    , "function "
    , "(" , sepBy (pure . stringifyName Local <$> args) ", " , ")\n"
    , stringify (S n) body , "\n" , indent n , "end" ]
  stringify n (LReturn x) = [ indent n , "return \n" , stringify (S n) x , "\n" , indent n , "" ]
  stringify n (LAssign (Just vis) x y) =
    [ indent n
    , stringifyVisibility vis
    , "\n"
    , stringify n x
    , " =\n"
    , stringify (n + 2) y
    ]
  stringify n (LAssign Nothing x y) =
    [ stringify n x , " =\n" , stringify (S n) y ]
  stringify n (LIfThenElse cond x y) =
    [ indent n , "if\n"
    , stringify (S n) cond
    , "\n"
    , indent n
    , "then\n"
    , stringify (S n) x , "\n"
    , indent n
    , "else\n"
    , stringify (S n) y
    , "\n"
    , indent n
    , "end" ]
  stringify n LBreak = [indent n, "break"]
  stringify n (LWhile cond body) =
    [ indent n
    , "while\n"
    , stringify (S n) cond
    , "\n"
    , indent n
    , "do\n"
    , stringify (S n) body
    , "\n"
    , indent n
    , "end" ]
  stringify n LDoNothing = [""]
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
  stringify n (LPrimFn (Neg ty) [x]) = [indent n, "- (", stringify Z x, ")"]
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
  stringify n (LPrimFn StrLength [x]) = [ indent n , "utf8.len(\n" , stringify (S n) x , ")" ]
  stringify n (LPrimFn StrHead [x]) = [ indent n , "utf8.sub(\n" , stringify (S n) x , ", 1, 1)" ]
  stringify n (LPrimFn StrTail [x]) = [ indent n , "utf8.sub(\n" , stringify (S n) x , ", 2)" ]
  stringify n (LPrimFn StrIndex [str, i]) =
      let strI = stringify (S n) i in
         [ indent n , "utf8.sub(\n" , stringify (S n) str
         , ",\n" , strI , ",\n"
         , strI , ")" ]
  stringify n (LPrimFn StrCons [x, xs]) =
    [ indent n , "(\n" , stringify (S n) x , ") .. (\n"
    , stringify (S n) xs , ")" ]
  stringify n (LPrimFn StrAppend [x, xs]) =
    [ indent n , "(\n" , stringify (S n) x , ") .. (\n"
    , stringify (S n) xs , ")" ]
  stringify n (LPrimFn StrReverse [x]) = [ indent n , "(\n" , stringify (S n) x , "):reverse()" ]
  stringify n (LPrimFn StrSubstr [offset, len, str]) =
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



  stringify n (LPrimFn (Cast StringType IntType) [x]) = stringifyFnApp n "strtointeger" [x] --defined in support
  stringify n (LPrimFn (Cast StringType DoubleType) [x]) = stringifyFnApp n "tonumber" [x]
  stringify n (LPrimFn (Cast StringType IntegerType) [x]) = stringifyFnApp n "bigint:new" [x]


  stringify n (LPrimFn (Cast IntType CharType) [x]) = [ indent n , "utf8.char(\n" , stringify (S n) x , ")" ]
  stringify n (LPrimFn (Cast IntType DoubleType) [x]) = stringify n x
  stringify n (LPrimFn (Cast IntType IntegerType) [x]) = stringifyFnApp n "bigint:new" [x]


  stringify n (LPrimFn (Cast CharType IntegerType) [x]) = [ indent n , "bigint:new(utf8.byte(\n" , stringify (S n) x , "))" ]
  stringify n (LPrimFn (Cast CharType IntType) [x]) = [ indent n , "utf8.byte(\n" , stringify (S n) x , ")" ]


  stringify n (LPrimFn (Cast IntegerType DoubleType) [x]) = stringifyFnApp n "bigint.tonumber" [x]
  stringify n (LPrimFn (Cast IntegerType IntType) [x]) = stringifyFnApp n "bigint.tonumber" [x]
  stringify n (LPrimFn (Cast IntegerType StringType) [x]) = stringifyFnApp n "bigint.tostring" [x]


  stringify n (LPrimFn (Cast DoubleType IntType) [x]) = stringifyFnApp n "math.floor" [x]
  stringify n (LPrimFn (Cast DoubleType IntegerType) [x]) =
    [ indent n , "bigint:new(math.floor(\n" , stringify (S n) x , "))" ]


  stringify n (LPrimFn (Cast ty StringType) [x]) = stringifyFnApp n "tostring" [x]
  stringify n (LPrimFn (Cast from to) [x]) =
    [ stringify n $ mkErrorAst $ "invalid cast: from " ++ show from ++ " to " ++ show to ]
  stringify n (LPrimFn BelieveMe [_, _, x]) = stringify n x
  stringify n (LPrimFn Crash [_, msg])
   = let ast = mkCrashAst msg in
         [stringify n ast]
  stringify n (LPrimFn op args) = stringify n $ mkErrorAst $ "unsupported primitive function: " ++ show op


-- replaceNames : List(Name, LuaExpr) -> LuaExpr -> LuaExpr
-- replaceNames names (LVar x) =
--   case lookup x names of
--        Nothing => LVar x
--        Just e => e
-- replaceNames names (LDeclVar v n) = LDeclVar v n
-- replaceNames names (LLambda args body) =
--   LLambda args $ replaceNames names body
-- replaceNames names (LApp x args) =
--   LApp (replaceNames names x) (replaceNames names <$> args)
-- replaceNames names (LPrimFn name args) = LPrimFn name (replaceNames names <$> args)
-- replaceNames names LNil = LNil
-- replaceNames names LTrue = LTrue
-- replaceNames names LFalse = LFalse
-- replaceNames names (LNumber x) = LNumber x
-- replaceNames names (LString x) = LString x
-- replaceNames names (LBigInt x) = LBigInt x
-- replaceNames names (LIndex expr key) = LIndex (replaceNames names expr) (replaceNames names key)
-- replaceNames names (LTable ys) =
--   LTable (map (\(key, val) => (
--                    replaceNames names key,
--                    replaceNames names val)) ys)
-- replaceNames names (LSeq x y) = LSeq (replaceNames names x) (replaceNames names y)
-- replaceNames names (LFnDecl vis name args body) = LFnDecl vis name args (replaceNames names body)
-- replaceNames names (LReturn x) = LReturn (replaceNames names x)
-- replaceNames names (LAssign Nothing x y) = LAssign Nothing (replaceNames names x) (replaceNames names y) --assignment
-- replaceNames names (LAssign (Just v) x y) = LAssign (Just v) x (replaceNames names y) --declaration with initial value
-- replaceNames names (LIfThenElse cond tr fa) =
--   LIfThenElse (replaceNames names cond) (replaceNames names tr)
--     (replaceNames names fa)
-- replaceNames names LBreak = LBreak
-- replaceNames names (LWhile cond body) = LWhile (replaceNames names cond) (replaceNames names body)
-- replaceNames names LDoNothing = LDoNothing
-- replaceNames names (LComment s) = LComment s

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

||| returns number of local variables in popped frame
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


mutual -- TODO try remove in favour of forward declarions ?

  uninhabNS : Namespace
  uninhabNS = preludeNS <.> mkNamespace "Uninhabited"

  iorefNS : Namespace
  iorefNS = mkNamespace "Data" <.> mkNamespace "IORef"

  stringsNS : Namespace
  stringsNS = mkNamespace "Data" <.> mkNamespace "Strings"

  arrayNS : Namespace
  arrayNS = mkNamespace "Data" <.> mkNamespace "IOArray" <.> mkNamespace "Prims"

  systemNS : Namespace
  systemNS = mkNamespace "System"

  infoNS : Namespace
  infoNS = mkNamespace "System" <.> mkNamespace "Info"

  ioNS : Namespace
  ioNS = preludeNS <.> mkNamespace "IO"

  extNames : List Name
  extNames = [mkNamespacedName (Just iorefNS) "prim__newIORef"
             ,mkNamespacedName (Just iorefNS) "prim__readIORef"
             ,mkNamespacedName (Just iorefNS) "prim__writeIORef"
             ,mkNamespacedName (Just arrayNS) "prim__newArray"
             ,mkNamespacedName (Just arrayNS) "prim__arrayGet"
             ,mkNamespacedName (Just arrayNS) "prim__arraySet"
             ,mkNamespacedName (Just infoNS)  "prim__os"
             ,mkNamespacedName (Just uninhabNS) "void"] --TODO add other implemented names

  foreignImpls : List Name
  foreignImpls = [ mkNamespacedName (Just preludeNS) "prim__putStr"
                 , mkNamespacedName (Just preludeNS) "prim__getStr"
                 , mkNamespacedName (Just systemNS) "prim__getArgs"
                 , mkNamespacedName (Just stringsNS) "fastConcat"
                 , mkNamespacedName (Just typesNS) "fastPack"
                 ]

  processCustomExtCall :
         {auto stack : Ref Stack StackSt}
      -> {auto frame : StackFrame}
      -> {auto opts : COpts}
      -> Name
      -> List NamedCExp
      -> Core LuaBlock
  processCustomExtCall name args
   = do (blocks, args) <- unzip <$> traverse processExpr args
        pure $ (concat blocks, LApp (LGVar $ UN $ nameRoot name) args)


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
                         pure (concat blockA, LApp (LGVar name) args) --defined in support file
                    _ => processCustomExtCall name args )
             ,
             ( pure $ ns == uninhabNS
             , case n of
                    "void" =>
                       do
                         args' <- traverse processExpr args
                         let (blockA, args) = unzip args'
                         pure (concat blockA, LApp (LGVar name) args) --defined in support file
                    _ => processCustomExtCall name args )
             ,
             ( pure $ ns == ioNS
             , case n of
                    "prim__onCollectAny" =>
                       do
                         args' <- traverse processExpr args
                         let (blockA, args) = unzip args'
                         pure (concat blockA, LApp (LGVar name) args) --defined in support file
                    "prim__onCollect" =>
                       do
                         args' <- traverse processExpr args
                         let (blockA, args) = unzip args'
                         pure (concat blockA, LApp (LGVar name) args) --defined in support file
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

  -- If there is only one hint line, assume its not prefixed with 'lua:'
  -- If there are multiple (it is hardly possible) find a line prefixed with 'lua:'
  searchForeign : List String -> Maybe (String, Maybe (List (String, String)))
  searchForeign [] = Nothing
  searchForeign (a :: b :: xs) = searchForeign' (a ::: (b :: xs))
  searchForeign [def] =
    let (def, req) = break (== '|') def in
        Just (def, if req == "" then Nothing else Just $ processRequire $ drop 1 req)

  --Foreign definition
  --may be implemented as a function / binding
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
           do --TODO refine this, use special namespace (table) for userdefined assignments
              let ((def, maybeReq), replace)
                  = ((\x => (x, True)) <$> (searchForeign hints)) `orElse` ((stringifyName Global name, Nothing), False)
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
      conVar <- pushLocal
      alts <- traverse (processConsAlt conVar) alts
      let table = LTable (replicate (alts |> length) (LDoNothing, LNil)) --preallocate space
      tableVar <- pushLocal
      let assignments = (\(k, v) => LAssign Nothing (LIndex tableVar k) v) <$> alts
      mdef <- lift $ processExpr <$> def
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
      mdef <- lift $ processExpr <$> def
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
      -- let args = (\(arg, i) => LApp (LVar ifThenElseName) --nil check before any table construction TODO this is for debug only
      --                [LPrimFn (EQ IntType) [arg, LNil]
      --                , LLambda [] $ mkErrorAst ("arg" ++ show i ++ " is nil")
      --                , LLambda [] $ LReturn $ arg])
      --                <$> zip args [1..args.length]
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
     -> Core (LuaExpr {-const-}, LuaExpr{-arm-})
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

  processDef :
           {auto c: Ref Stack StackSt}
        -> {auto opts : COpts}
        -> {auto refs : Ref Ctxt Defs}
        -> {auto preamble : Ref Preamble PreambleSt}
        -> (Name, FC, NamedDef)
        -> Core LuaExpr {-block of code-}
  processDef (n, _, MkNmFun args expr) =
   if (find (== n) extNames) |> isJust
      then
         pure LDoNothing --do not gen names for ext fns and foreign fns, done separately
      else do
         newFrame <- pushFrame
         (blockA, expr) <- processExpr {frame = newFrame} expr
         vars <- popFrame
         pure $ LFnDecl n args $ declFrameTable newFrame vars
                                <+> blockA
                                <+> (LReturn expr) --paste code block into function def

  processDef (n, _, MkNmError expr) =
    throw $ (InternalError (show expr))
  processDef (n, _, MkNmForeign hints argsty retty) = --those are added into the preamble
    do
      processForeignDef n hints argsty retty
      pure LDoNothing
  processDef (n, _, MkNmCon _ _ _) =
    pure LDoNothing  --we do not need to predefine structures in lua


builtinSupportDefs : List LuaExpr -- add top level lua defs from here or through support library
builtinSupportDefs = []


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
      pure $ MkCOptsInfo
               (thisOrDefault (opt1 >>= parseEnvBool))
               (thisOrDefault (opt2 >>= parseEnvBool))
               (MkWithDefault opt3 _)
               (thisOrDefault (opt4 >>= parseEnvBool))
               (thisOrDefault (opt5 >>= parseEnvBool))

-- printDefs : List (Name, FC, NamedDef) -> List (Name, GlobalDef) -> Core ()
-- printDefs ndefs gdefs = (logLine . delay . foldl (++) "" . map toString) ndefs
--   where
--     toString : (Name, FC, NamedDef) -> String
--     toString (n, _, d) = "def:\n   " ++ show n ++ "\n"
--                      ++ "ty:\n   " ++ show (type <$> lookup n gdefs) ++ "\n"
--                      ++ "case tree:\n   " ++ show d ++ "\n\n"

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
  -- let gdefs = cdata.globalDefs
  --printDefs ndefs gdefs
  let ctm = forget cdata.mainExpr
  clock2 <- coreLift $ clockTime Monotonic
  logLine $ "Looked up direct names [2/5] in " ++ showMillis (toMillis $ timeDifference clock2 clock1)
  let ndefs = defsUsedByNamedCExp ctm ndefs -- work through relevant names only
  s <- newRef Stack (MkStackSt [] frameLowest indexLowest)
  pr <- newRef Preamble (MkPreambleSt empty)
  cdefs <- traverse processDef (reverse ndefs)
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


  let stringPlan : DeferedStr =
             [ " --------- SUPPORT DEFS ---------\n"
             , "idris = {}\n"
             , "idris.null = {}\n"
             , "local null = idris.null\n"
             , "idris.luaVersion = " ++ show (opts |> luaVersion |> get |> index) ++ "\n" --sets target Lua version to be used in support
             , "idris.noRequire  = " ++ (toLower . show) (opts |> noRequire |> get) ++ "\n"
             , support , "\n"
             , stringify Z (concat builtinSupportDefs)
             , "local idris = idris"
             , "\n---------- PREAMBLE DEFS ----------\n"
             , join "\n" (preamble |> values) , "\n\n"
             , "\n---------- CTX DEFS ----------\n"
             , stringify Z con_cdefs
             , "\n--------- RETURN ---------\n"
             , stringify Z frameTable, "\n"
             , stringify Z block     , "\n"
             , stringify Z main]
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

build : Ref Ctxt Defs --TODO add option to build only .lua file
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
  _ <- coreLift $ system $ "'" ++ exe ++ "' "
  pure ()

luaCodegen : Codegen
luaCodegen = MkCG compile execute

export
main : IO ()
main = mainWithCodegens [("lua", luaCodegen)]
