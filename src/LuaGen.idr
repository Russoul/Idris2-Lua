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
import System.Clock
import Data.Bool.Extra
import Data.Strings
import Data.String.Extra as StrExtra
import Data.SortedMap
import Utils.Path
import Utils.Hex
import public LuaCommon
import public LuaAst


data Stack : Type where
data Preamble : Type where
data LuaCode : Type where


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
   -> String
   -> Core ()
logLine str with (opts.debugOutput.get)
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

mkErrorAst : String -> LuaExpr
mkErrorAst str = 
    LApp (LGVar (UN "error")) [LString str]
mkErrorAst' : LuaExpr -> LuaExpr
mkErrorAst' str = 
    LApp (LGVar (UN "error")) [str]


ifThenElseName : Name
ifThenElseName = UN "idris__ifThenElse"

getArgsName : Name
getArgsName = UN "idris__getArgs"

stringifyNameGlobal : Name -> String
stringifyNameGlobal (NS ns n) = join "." (reverse ns) ++ "." ++ stringifyNameGlobal n
stringifyNameGlobal (UN x) = x
stringifyNameGlobal (MN x y) = "{" ++ x ++ ":" ++ show y ++ "}"
stringifyNameGlobal (PV n d) = "{P:" ++ stringifyNameGlobal n ++ ":" ++ show d ++ "}"
stringifyNameGlobal (DN _ n) = stringifyNameGlobal n
stringifyNameGlobal (Nested (outer, idx) inner)
    = show outer ++ ":" ++ show idx ++ ":" ++ stringifyNameGlobal inner
stringifyNameGlobal (CaseBlock outer i) = "case[" ++ show i ++ "]" ++ outer
stringifyNameGlobal (WithBlock outer i) = "with[" ++ show i ++ "]" ++ outer
stringifyNameGlobal (Resolved x) = "$resolved" ++ show x

stringifyNameMangle : Name -> String
stringifyNameMangle (NS ns n) = join "_" (validateIdentifier <$> reverse ns) ++ "_" ++ stringifyNameMangle n
stringifyNameMangle (UN x) = validateIdentifier x
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
    ,sepBy (stringify (S n) <$> args.toList) ",\n" 
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
                              <$> chars.head' `orElse` False) 
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
                                        <$> chars.head' `orElse` False) 
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
  stringify n (LPrimFn (Div IntType) [x, y]) with (copts.luaVersion.get >= Lua53) 
     stringify n (LPrimFn (Div IntType) [x, y]) | True
       = stringifyBinOp n "//" x y
     stringify n (LPrimFn (Div IntType) [x, y]) | False 
       = stringifyFnApp n "idris.div" [x, y]
  stringify n (LPrimFn (Div IntegerType) [x, y]) = stringifyBinOp n "/" x y
  stringify n (LPrimFn (Div DoubleType) [x, y]) = stringifyBinOp n "/" x y
  stringify n (LPrimFn (Mod ty) [x ,y]) = stringifyBinOp n "%" x y
  stringify n (LPrimFn (Neg ty) [x]) = [indent n, "- (", stringify Z x, ")"]
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



  stringify n (LPrimFn (Cast StringType IntType) [x]) = stringifyFnApp n "tonumber" [x] 
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
  stringify n (LPrimFn Crash [_, msg]) = stringify n $ mkErrorAst' msg 
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
  pure $ LAssign Nothing retn LNil --retn is by default initialized to `nil`


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
             ,NS ["Uninhabited", "Prelude"] (UN "void")] --TODO add other implemented names

  --fully applied external name
  --can be inlined
  --THIS IS NOT A DEFINITION !
  processExtCall : 
         {auto stack : Ref Stack StackSt}
      -> {auto frame : StackFrame}
      -> {auto opts : COpts}
      -> Name
      -> List NamedCExp
      -> Core LuaBlock
  processExtCall (NS ["IORef", "Data"] (UN "prim__newIORef")) [_, v, _] =
    do
      (blockA, v) <- processExpr v
      pure (blockA, LTable [(LString "val", v)])
  processExtCall (NS ["IORef", "Data"] (UN "prim__readIORef")) [_, r, _] =
    do
      (blockA, r) <- processExpr r
      pure (blockA, LIndex r (LString "val"))
  processExtCall (NS ["IORef", "Data"] (UN "prim__writeIORef")) [_, r, v, _] = 
    do
      (blockA, r) <- processExpr r
      (blockB, v) <- processExpr v
      pure (blockA <+> blockB <+> LAssign Nothing (LIndex r (LString "val")) v, LTable [(LString "tag", LString "0")] {-Unit-})
  processExtCall (NS ["Prims", "IOArray", "Data"] (UN "prim__newArray")) [_, len, init, _] = 
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
      pure (blockA <+> blockB <+> blockC <+> LAssign Nothing (LIndex ar (LPrimFn (Add IntType) [i, LNumber "1"])) v, LTable [(LString "tag", LString "0")] {-Unit-}) 
  processExtCall name@(NS ["PrimIO"] (UN "prim__schemeCall")) args = 
    do
      args' <- traverse processExpr args
      let (blockA, args) = unzip args'
      pure (concat blockA, LApp (LGVar name) args) --defined in support file
  processExtCall name@(NS ["Info", "System"] (UN "prim__os")) args =
    do
      args' <- traverse processExpr args
      let (blockA, args) = unzip args'
      pure (concat blockA, LApp (LGVar name) args) --defined in support file
  processExtCall name@(NS ["Uninhabited", "Prelude"] (UN "void")) args = 
    do
      args' <- traverse processExpr args
      let (blockA, args) = unzip args'
      pure (concat blockA, LApp (LGVar name) args) --defined in support file
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
          {auto defs : Ref Ctxt Defs} 
       -> {auto opts : COpts}
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
  processForeignDef name hints argtys retty = do --TODO refine this, use special namespace (table) for userdefined assignments
      let ((def, maybeReq), replace) 
          = ((\x => (x, True)) <$> (searchForeign hints)).orElse ((stringifyName Global name, Nothing), False)
      log 2 $ "using %foreign " ++ def
      case maybeReq of
           (Just pack) => do 
                         log 2 $ "requiring " ++ pack
                         addDefToPreamble 
                          ("$" ++ pack) 
                           ((stringifyName Global (UN pack)) ++ " = require('" ++ pack ++ "')")
                            True -- its ok to require the same package multiple times, ignore all but first

                                                             -- '$' makes sure all require statements
                                                             -- are above assingnments using them
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
      let table = LTable (replicate alts.length (LDoNothing, LNil)) --preallocate space
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
      let table = LTable (replicate alts.length (LDoNothing, LNil)) --preallocate space
      tableVar <- pushLocal
      let assignments = (\(k, v) => LAssign Nothing (LIndex tableVar k) v) <$> alts
      mdef <- lift $ processExpr <$> def
      index <- 
          (\alt => constCaseIndex alt constVar) 
          <$> head' rawalts `orElse` pure LNil --orElse is in case there is only default branch of case clause
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
      let conArgs = zipWith (\i, arg => (LString $ "arg" ++ (show i), arg)) [1..args.length] args
      let mbName = if opts.storeConstructorName.get then [(LString "name", LString $ stringifyName Global n), (LString "num", LNumber $ show args.length)] else []
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
                [1..args.length] args --TODO use stack instread of let bindings, replace names
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
   if (find (== n) extNames) .isJust
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


getCOpts : Core COpts
getCOpts = 
   do
      opt1 <- coreLift $ getEnv "StoreConsName"
      opt2 <- coreLift $ getEnv "DynSupport"
      (Just opt3) <- coreLift $ do str <- getEnv "LuaVersion"
                                   pure (parseLuaVersion <<= str)
         | _ => throw (UserError "Could not parse Lua version from $LuaVersion, format: X.X[.X]")
      opt4 <- coreLift $ getEnv "NoRequire"
      opt5 <- coreLift $ getEnv "DebugOutput"
      pure $ MkCOptsInfo 
               (thisOrDefault (opt1 >>= parseEnvBool)) 
               (thisOrDefault (opt2 >>= parseEnvBool)) 
               (MkWithDefault opt3 _) 
               (thisOrDefault (opt4 >>= parseEnvBool))
               (thisOrDefault (opt5 >>= parseEnvBool))


translate : Ref Ctxt Defs -> ClosedTerm -> Core StrBuffer
translate defs term = do
  opts <- getCOpts
  clock0 <- coreLift $ clockTime Monotonic
  logLine "Lua compilation started [0/5]"
  logLine ("Using " ++ show opts.luaVersion.get)
  cdata <- getCompileData Cases term
  clock1 <- coreLift $ clockTime Monotonic
  logLine $ "Got compile data [1/5] in " ++ showMillis (toMillis $ timeDifference clock1 clock0)
  let ndefs = cdata.namedDefs
  let ctm = forget cdata.mainExpr
  clock2 <- coreLift $ clockTime Monotonic
  logLine $ "Looked up direct names [2/5] in " ++ showMillis (toMillis $ timeDifference clock2 clock1)
  --let used = defsUsedByNamedCExp ctm ndefs 
  s <- newRef Stack (MkStackSt [] frameLowest indexLowest)
  pr <- newRef Preamble (MkPreambleSt empty)
  cdefs <- traverse processDef ndefs.reverse
  clock3 <- coreLift $ clockTime Monotonic
  logLine $ "Compiled definitions [3/5] in " ++ showMillis (toMillis $ timeDifference clock3 clock2)
  let con_cdefs = concat cdefs
  --TODO tail call optimization
  frame <- pushFrame
  (block, main) <- processExpr {frame = frame} ctm
  vars <- popFrame
  let frameTable = declFrameTable frame vars
  clock4 <- coreLift $ clockTime Monotonic
  logLine $ "Compiled main [4/5] in " ++ showMillis (toMillis $ timeDifference clock4 clock3)
  preamble <- getPreamble

  support <- if opts.dynamicSupportLib.get
                   then
                     pure "require(\"idris2-lua\")"
                   else
                     readDataFile $ "lua" </> "idris2-lua.lua"


  let stringPlan : DeferedStr =
             [ " --------- SUPPORT DEFS ---------\n"
             , "idris = {}\n"
             , "idris.null = {}\n"
             , "local null = idris.null\n"
             , "idris.luaVersion = " ++ show (index opts.luaVersion.get) ++ "\n" --sets target Lua version to be used in support
             , "idris.noRequire  = " ++ (toLower . show) opts.noRequire.get ++ "\n"
             , support , "\n" 
             , stringify Z (concat builtinSupportDefs)
             , "local idris = idris"
             , "\n---------- PREAMBLE DEFS ----------\n"
             , join "\n" preamble.values , "\n\n"
             , "\n---------- CTX DEFS ----------\n"
             , stringify Z con_cdefs
             , "\n--------- RETURN ---------\n"
             , stringify Z frameTable
             , stringify Z block
             , stringify Z main]
  let mbyte = 1024 * 1024           
  strbuf <- newRef LuaCode !(allocStrBuffer mbyte)
  traverse_ (writeStr LuaCode) stringPlan
  clock5 <- coreLift $ clockTime Monotonic
  logLine $ "Stringified lua [5/5] in " ++ showMillis (toMillis $ timeDifference clock5 clock4)
  logLine $ "All done in " ++ showMillis (toMillis $ timeDifference clock5 clock0)
  strbuf <- get LuaCode
  pure strbuf

compile : Ref Ctxt Defs -> (tmpDir : String) -> (outputDir : String) ->
        ClosedTerm -> (outfile : String) -> Core (Maybe String)
compile defs tmpDir outputDir term file = do 
   
  strbuf <- translate defs term
  Right () <- coreLift $ writeBufferToFile (outputDir </> file) strbuf.get strbuf.offset
    | Left err => do coreLift $ freeBuffer strbuf.get; throw $ FileErr (outputDir </> file) err
  coreLift $ freeBuffer strbuf.get
    
  pure $ Just (outputDir </> file)

execute : Ref Ctxt Defs -> (tmpDir : String) -> ClosedTerm -> Core ()
execute defs tmpDir term = do
  strbuf <- translate defs term
  let file = "generated.lua"
  lua <- coreLift $
    do
      mbDefined <- getEnv "LuaExe" 
      pure $ mbDefined `orElse` "lua"
  
  Right () <- coreLift $ writeBufferToFile (tmpDir </> file) strbuf.get strbuf.offset
    | Left err => do coreLift $ freeBuffer strbuf.get; throw $ FileErr (tmpDir </> file) err
  coreLift $ freeBuffer strbuf.get
  _ <- coreLift $ system $ "'" ++ lua ++ "' " ++ show (tmpDir </> file)
  pure ()

luaCodegen : Codegen
luaCodegen = MkCG compile execute


export
main : IO ()
main = mainWithCodegens [("lua", luaCodegen)]



