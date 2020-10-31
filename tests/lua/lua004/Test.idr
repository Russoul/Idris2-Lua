module Test

import Data.Vect
import System.File
import System
import Data.Buffer
import Data.Strings

test1 : Nat -> List String -> Vect n Int -> String
test1 1 (x :: xs) (y :: ys) = show 1 ++ show x ++ show xs ++ show y ++ show ys
test1 0 [] [x] = "m1 " ++ show x
test1 2 (x :: xs) (y :: []) = "m2 " ++ show x ++ show xs ++ show y
test1 (S k) d t = "m3 " ++ let x = test1 k (show k :: d) t in x
test1 k d t = "m4 " ++ show k ++ show d ++ show t


data MyDat = A1 | A2 | A3 | A4 | A5 | A6 | A7 | A8

Show MyDat where
   show A1 = "A1"
   show A2 = "A2"
   show A3 = "A3"
   show A4 = "A4"
   show A5 = "A5"
   show A6 = "A6"
   show A7 = "A7"
   show A8 = "A8"

ansiColorStr : String -> Vect 3 Int -> String
ansiColorStr str [r, g, b] = "\x1b[38;2;" ++ show r ++ ";" ++ show g ++ ";" ++ show b ++  "m" ++ str ++ "\x1b[0m"

namespace Either
   public export
   ignoreErr : (Show a) => IO (Either a b) -> IO b
   ignoreErr io =
      do
         (Right ok) <- io
            | Left err =>
                        do
                           putStrLn $ show err
                           exitFailure
         pure ok

namespace Maybe
   public export
   ignoreErr : IO (Maybe a) -> IO a
   ignoreErr io =
      do
         (Just ok) <- io
            | Nothing =>
                        do
                           putStrLn "Got nothing"
                           exitFailure
         pure ok

main : IO ()
main = do
   let aα = the Nat 5
   putStrLn $ show aα
   putStrLn $ test1 1 ["a", "b"] [2, 3, 4, 5]
   putStrLn $ test1 0 [] [6]
   putStrLn $ test1 2 ["c", "d", "e"] [1]
   putStrLn $ test1 3 ["p", "t"] [0]
   putStrLn $ test1 4 ["a"] [0, 1, 2, 3]
   putChar 'c'
   putChar 'b'
   putChar '\n'
   putStrLn $ show A1
   putStrLn $ show A8
   putStrLn $ show A6
   f <- ignoreErr $ openFile "data4.txt" Read
   putStrLn $ show !(fGetLine f)
   putStrLn $ show !(fEOF f)
   putStrLn $ show !(fileModifiedTime f)
   fPutStrLn stdout "\x1b[38;2;255;100;0mThis is error\x1b[0m"
   closeFile f
   writeFile "data.txt" $ ansiColorStr "red\n" [255, 0, 0]
     ++ ansiColorStr "green\n" [0, 255, 0]
     ++ ansiColorStr "blue" [0, 0, 255]
   putStrLn $ show (the Int 257)
   putStrLn $ show !(ignoreErr $ readFile "data.txt")
   buf <- ignoreErr $ createBufferFromFile "data.txt"
   size <- rawSize buf
   putStrLn $ "buf size " ++ show size
   putStrLn $ "buf contents:\n" ++ !(getString buf 0 size)
   let i64s = 8
   ibuf <- ignoreErr $ newBuffer (i64s * 10)
   putStrLn $ "init size" ++ show !(rawSize ibuf)
   let list = [0..9]
   traverse (\i => do setInt ibuf (i64s * i) i;putStrLn $ "next size" ++ show !(rawSize ibuf)) list
   --setInt31 ibuf 114 (-991133)
   setInt ibuf 114 (-567)
   setDouble ibuf 122 (-241.123456789)
   setString ibuf 80 "hi there !"
   setString ibuf 90 "русский язык"
   dat2 <- ignoreErr $ openFile "data2.txt" WriteTruncate
   writeBufferData dat2 ibuf 0 !(rawSize ibuf)
   putStrLn $ show $ !(getInt ibuf 0 )
   putStrLn $ show $ !(getInt ibuf 8 )
   putStrLn $ show $ !(getInt ibuf (8 * 9) )
   closeFile dat2
   ibuf <- ignoreErr $ createBufferFromFile "data2.txt"
   putStrLn $ show $ !(getInt ibuf 0 )
   putStrLn $ show $ !(getInt ibuf 8 )
   putStrLn $ show $ !(getInt ibuf (8 * 9) )
   putStrLn $ show !(rawSize ibuf)
   putStrLn !(getString ibuf 80 10)
   putStrLn !(getString ibuf 90 24)
   putStrLn $ show !(getInt ibuf 114)
   putStrLn $ show !(getDouble ibuf 122)
