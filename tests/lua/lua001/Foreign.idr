import Data.HVect

-- Signature of a %foreign hint:
-- definition|require1(renameRequire1), require2(renameRequire2), ...

%foreign "function () end|inspect, extra"
imports : PrimIO ()

-- This function does nothing at runtime
-- But we need to reference it from any runtime relevant function, to make sure idris
-- includes 'imports' definition at runtime
-- otherwise all 'require' statements, like 'inspect' and 'extra', won't be generated
doImports : IO ()
doImports = primIO imports

%foreign "function(_, x) return idris.inspect(x) end"
inspect : a -> String

-- Keep in mind that erased arguments are still present in function signatures,
-- though they are always passed as 'nil'
-- I think we should fix this behaviour, but it originates within the Idris compiler
%foreign "function(_, x) return idris.inspect(x) end"
inspectList : List a -> String

-- 'a : Type' and 'b : Type' are erased, thus two underscores
%foreign "function(_, _, f, x) return idris.extra.apply(f, x) end"
apply : (a -> b) -> a -> b

%foreign "function(_, list) return idris.extra.printList(list) end"
printList : List a -> String

-- Represents Lua dictionaries
data Dict : Type where [external]

-- Here we silently have another implicit argument of type Nat: length of 'tyes'
%foreign "function(_, _, hv) return idris.extra.hVectToDict(hv, {}) end"
toDict : HVect tyes -> Dict
-- toDict : {0 n: Nat} -> {0 tyes : Vect n Type} -> HVect tyes -> Dict

-- for demonstration purposes lets require 'extra' renaming it to 'extras'
%foreign "function(f) return idris.extras.apply(f, 1) end|extra(extras)"
applyTo1 : (Int -> Int) -> Int

main : IO ()
main = do doImports
          putStrLn $ inspect "hey"
          putStrLn $ inspectList [1, 2, 3, the Int 4, 5]
          putStrLn $ show $ applyTo1 (* 2)
          putStrLn $ show $ Main.apply (+ 1) (the Int 1)
          putStrLn $ printList [1, the Int 2, 3, the Int 4]
          putStrLn $ inspect $ toDict [("a", the Int 1), ("b", "b"), ("c", the (List Integer) [1, 2, 3])]
