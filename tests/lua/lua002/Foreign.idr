import Data.Strings

main : IO ()
main = do putStrLn $ fastPack ['a', 'b', 'c', 'π', 'Ω', '2']
          printLn $ fastUnpack "abcπΩ2"
          putStrLn $ fastConcat ["a", "b", "c", "πΩ", "2"]
