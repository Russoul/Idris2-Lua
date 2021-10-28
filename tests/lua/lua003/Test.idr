
import Data.Vect
import Data.IORef
import Data.IOArray
import Data.String
import Data.Vect
import Data.List
import System
data MyData = MyCons0 Nat | MyCons1


Show MyData where
  show (MyCons0 x) = "blah" ++ show x
  show MyCons1 = "babah"

boom : Nat -> Nat
boom (S k) = boom k
boom Z = 32

whatData : MyData -> Nat
whatData (MyCons0 x) = x
whatData MyCons1 = 99


factorial : Integer -> Integer -> Integer
factorial 0 ac = ac
factorial x ac = factorial (x - 1) (ac * x)

data BTree a = BBranch (BTree a) a (BTree a) | BLeaf


intPow : Integer -> Integer -> Integer
intPow base exp =
  if exp > 1 then base * (intPow base (exp - 1)) else if exp == 1 then base else 1


fillIn : Nat -> List Nat -> (Nat -> Nat -> a) -> BTree a
fillIn Z _ f = BLeaf
fillIn (S k) l f =
  BBranch
   (fillIn k (0 :: l) f)
    (f k $ count k (reverse l))
     (fillIn k (1 :: l) f)
where
  count : Nat -> List Nat -> Nat
  count k (x :: xs) = let len = length xs in x * (integerToNat $ intPow 2 (cast len)) + count k xs
  count _ [] = 0

printLeft : Show a => BTree a -> String
printLeft BLeaf = ""
printLeft (BBranch l x r) = printLeft l ++ " " ++ show x ++ " " ++ printLeft r

indent : Nat -> String
indent k = pack $ replicate (2 * k) ' '

Cast Nat String where
  cast x = cast $ cast {to = Int} x



testInteger : Integer -> Integer -> Integer
testInteger x y = x * x * x * x - 1

%hide Prelude.print

data Lua : Type where [external]

%foreign "lua:function (_) return function (x) return idris.inspect(x) end end|inspect"
inspect : (x : a) -> String

%foreign "lua:function(x) return function (str) return x[str] end end|inspect"
dot : Lua -> String -> Lua

%foreign "lua:function (x) return require (x) end"
require : String -> Lua

%foreign "lua:function(a) return function(b) return function(f) return function(x) return f(x) end end end end"
call : {0 a : Type} -> {0 b : Type} -> Lua -> a -> b



%foreign "lua:print"
print_ : String -> ()

print : (HasIO io) => String -> io ()
print x = pure $ print_ x


main : IO ()
main = do
  let ins = require "inspect"
  putStrLn $ call (ins `dot` "inspect") [1, 2, the Int 3] {a = List _} {b = String}

  v <- newIORef ""
  print "enter something:"
  writeIORef v !(getLine)
  print $ "you said " ++ !(readIORef v)
  putStrLn $ if 1 > 2 then "not ok" else "ok"
  printLn $ (the Int 1)
  putStrLn $ show (the Nat 28)
  putStrLn $ show $ whatData $ MyCons0 7
  ar <- newArray 10 {elem = Int}
  pure ()
  let from = the Int (fromInteger 10)
  putStrLn $ show $ "ok " ++ "or not"
  putStrLn $ show (5 == the Int 5)
  putStrLn $ show (0 == the Integer 0)
  putStrLn $ show (1 < the Integer 2)
  putStrLn $ show (7 < the Int 4)
  args <- getArgs
  traverse_ putStrLn args

  putStrLn $ show $ (the Integer 0) > 0
  putStrLn $ show $ testInteger 2 5
  putStrLn $ "2 ^ 6 == " ++ show (intPow 2 6)
  let  tr = fillIn 4 [] (\d, i => show d ++ " " ++ show i)
  putStrLn $ printLeft tr

  putStrLn $ "the guts of BTree look like this: " ++ inspect tr

  putStrLn $ show from
  putStrLn $ show $ (the Integer (2 - 2)) == 0
  putStrLn $ show $ factorial 1000 1
  putStrLn "unicode string: lambda λ, sigma Σ, integral ∫, cyrillic F Ф"
