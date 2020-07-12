module Test

import Data.Vect
import Data.IORef
import Data.IOArray
import Data.Strings
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
    (f k $ count k l.reverse)
     (fillIn k (1 :: l) f) 
where
  count : Nat -> List Nat -> Nat
  count k (x :: xs) = let len = xs.length in x * (integerToNat $ intPow 2 (cast len)) + count k xs
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

main : IO ()
main = do 
  v <- newIORef ""
  writeIORef v !(getLine)
  putStrLn $ "you said " ++ !(readIORef v)
  putStrLn $ if 1 > 2 then "not ok" else "ok"
  putStrLn $ show (the Nat 28)
  ar <- newArray 10 {elem = Int}
  pure ()
  let from = the Int (fromInteger 10)
  traverse (\i => writeArray ar i $ the Int i) [1 .. 8]
  list <- ar.toList
  putStrLn $ show $ list
  args <- getArgs
  traverse putStrLn args
 
  putStrLn $ show $ (the Integer 0) > 0
  putStrLn $ show $ testInteger 2 5
  putStrLn $ "2 ^ 6 == " ++ show (intPow 2 6)
  let  tr = fillIn 4 [] (\d, i => (cast d) ++ " " ++ (cast i))
  putStrLn $ printLeft tr 

  putStrLn $ show from
  putStrLn $ show $ (the Integer (2 - 2)) == 0
  putStrLn $ show $ factorial 100 1
  


