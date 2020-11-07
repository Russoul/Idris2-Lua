
namespace Lua
  export
  %foreign "x, y => x + y"
  plus : Int -> Int -> Int

  export -- there is now also a `W` local variable, accessible anywhere from FFI for convenience
         -- local W = '%MkWorld'
  %foreign "callback, _ => callback('abc')(22)(W)"
  callback : (callback : String -> Int -> PrimIO String) -> PrimIO String

  export
  %foreign "x => idris.inspect(x)|inspect"
  inspect : ty -> String

  export
  %foreign "x, y, f => f(x)(y)"
  apply2 : a -> (0 b : Type {- for demo purposes -}) -> b -> (a -> b -> c) -> c

  export
  %foreign "_ => print(W)"
  printWorld : IO ()

main : IO ()
main = do printLn $ Lua.plus 1 3
          str <- fromPrim $ callback (\str, i => toPrim $ pure $ str ++ " " ++ show i)
          putStrLn str
          putStrLn (inspect $ with List [the Int 1, 2, 3])
          putStrLn $ apply2 "abc" _ "def" (++)
          printWorld

