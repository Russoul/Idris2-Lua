import Data.IOArray

main : IO ()
main
    = do x <- newArray {io = IO, elem = String} 20
         ignore $ writeArray {io = IO} x 10 "Hello"
         ignore $ writeArray {io = IO} x 11 "World"
         printLn !(toList x)

         y <- fromList (map Just [1,2,3,4,5])
         printLn !(toList y)
