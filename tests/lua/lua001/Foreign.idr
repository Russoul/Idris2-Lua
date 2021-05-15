import Data.HVect
import System.Info

-- Signature of a %foreign hint:
-- definition|require1(renameRequire1), require2(renameRequire2), ...
-- prefix 'lua:' is optional if there is only one %foreign hint

-- All Idris functions are compiled as curried Lua lambdas, foreign functions are no different.

%foreign "lua:function () end|inspect, extra"
imports : PrimIO ()

-- This function does nothing at runtime
-- But we need to reference it from any runtime relevant function, to make sure idris
-- includes 'imports' definition at runtime
-- otherwise all 'require' statements, like 'inspect' and 'extra', won't be generated
doImports : IO ()
doImports = primIO imports

-- Make sure given names are present in compiled output
%foreign "function (_) return function(_) return function (_) return function(w) return {tag='0'} end end end end"
compile : HVect tyes -> IO ()

%foreign "function(_) return function(x) return idris.inspect(x) end end"
inspect : a -> String

-- Keep in mind that erased arguments are still present in function signatures,
-- though they are always passed as 'nil'
-- I think we should fix this behaviour, but it originates within the Idris compiler
%foreign "function(_) return function(x) return idris.inspect(x) end end"
inspectList : List a -> String

-- 'a : Type' and 'b : Type' are erased, thus two underscores
%foreign "function(_) return function(_) return function(f) return function(x) return idris.extra.apply(f, x) end end end end"
apply : (a -> b) -> a -> b

%foreign "function(_) return function(list) return idris.extra.printList(list) end end"
printList : List a -> String

-- Represents Lua dictionaries
data Dict : Type where [external]

-- Here we silently have another implicit argument of type Nat: length of 'tyes'
%foreign "function(_) return function(_) return function(hv) return idris.extra.hVectToDict(hv, {}) end end end"
toDict : HVect tyes -> Dict
-- toDict : {0 n: Nat} -> {0 tyes : Vect n Type} -> HVect tyes -> Dict

-- for demonstration purposes lets require 'extra' renaming it to 'extras'
%foreign "function(f) return idris.extras.apply(f, 1) end|extra(extras)"
applyTo1 : (Int -> Int) -> Int

%foreign "function(idrisPlus) return idrisPlus(1)(3) end"
four : (Int -> Int -> Int) -> Int

%foreign "function(f) return function(w) f('A string from Lua !')(w); return 'ok' end end"
callIdrisFromLua : (String -> IO String) -> IO String

barePrint : String -> IO ()
barePrint = putStrLn

%foreign "function(w) idris['Main.barePrint']('Another string from Lua !')(w); return 0 end"
callIdrisFromLua' : IO ()

main : IO ()
main = do doImports
          compile [barePrint]
          putStrLn $ inspect "hey"
          putStrLn $ inspectList [1, 2, 3, the Int 4, 5]
          putStrLn $ show $ applyTo1 (* 2)
          putStrLn $ show $ Main.apply (+ 1) (the Int 1)
          putStrLn $ printList [1, the Int 2, 3, the Int 4]
          putStrLn $ inspect $ toDict [("a", the Int 1), ("b", "b"), ("c", the (List Integer) [1, 2, 3])]
          putStrLn $ "is four " ++ show (four (+))
          ok <- callIdrisFromLua (\str => putStrLn str *> pure "ok")
          putStrLn $ "Got " ++ ok ++ " back"
          putStrLn $ inspect codegen
          () <- callIdrisFromLua'
          pure ()
