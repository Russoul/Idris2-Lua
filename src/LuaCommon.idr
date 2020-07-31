module LuaCommon


import Core.Core
import Core.Name
import Data.Strings
import Data.String.Extra as StrExtra
import Data.Vect
import Data.List
import Data.Buffer
import Utils.Hex
infixr 1 <<=

export
swap : (a -> b -> c) -> b -> a -> c
swap f x y = f y x

export
(<<=) : (Monad m) => (a -> m b) -> (m a) -> m b
(<<=) = swap (>>=)


public export
data LuaVersion = Lua51 | Lua52 | Lua53 | Lua54

namespace Strings
   public export
   ||| replaces all occurances of literal @lit 
   ||| in string @str 
   replaceAll : --TODO rename
         (lit : String) 
      -> (str : String)
      -> String
   replaceAll lit str with (str == "") 
      replaceAll lit str | False =  
         let other = replaceAll lit (substr (length lit) (length str `minus` length lit) str) in
             if isPrefixOf lit str
                then replaceAll lit (substr (length lit) (length str `minus` length lit) str)
                else case strUncons str of
                          Just (head, rest) => strCons head (replaceAll lit rest)
                          Nothing => ""
      replaceAll lit str | True = "" 
         

namespace LuaVersion

   export
   index : LuaVersion -> Int
   index Lua51 = 51
   index Lua52 = 52
   index Lua53 = 53
   index Lua54 = 54

   export
   fromIndex : Int -> Maybe LuaVersion
   fromIndex 51 = Just Lua51
   fromIndex 52 = Just Lua52
   fromIndex 53 = Just Lua53
   fromIndex 54 = Just Lua54
   fromIndex _  = Nothing
   
   export
   Eq LuaVersion where
      Lua51 == Lua51 = True
      Lua52 == Lua52 = True
      Lua53 == Lua53 = True
      Lua54 == Lua54 = True
      _     ==     _ = False

   export
   Show LuaVersion where
      show ver = 
       let index = index ver
           major = index `div` 10
           minor = index `mod` 10
       in
           "Lua" ++ show major ++ "." ++ show minor
   
   export
   Ord LuaVersion where
      compare v v' = compare (index v) (index v')



   export
   parseLuaVersion : String -> Maybe LuaVersion
   parseLuaVersion str = helper ((trim . toLower) str)
   where
      helper : String -> Maybe LuaVersion
      helper x = 
         let noprefix = 
                if isPrefixOf "lua" x
                  then drop 3 x
                  else x
             nodots = replaceAll "." noprefix
             nodashes = replaceAll "-" nodots
             firstTwo = take 2 nodashes
         in      
             do int <- parseInteger {a = Int} firstTwo
                fromIndex int



namespace Data.List
  export
  unzip : (xs : List (a, b)) -> (List a, List b)
  unzip ((l, r) :: xs) = 
    let (ls, rs) = unzip xs in
        (l :: ls, r :: rs)
  unzip [] = ([], [])      

namespace Data.Maybe
  export
  orElse : (maybe : Maybe a) -> Lazy a -> a
  orElse Nothing x = x
  orElse (Just x) _ = x

public export
luaKeywords : List String
luaKeywords = ["and", "break", "do", "else", "elseif", "end",
               "false", "for", "function", "goto", "if", "in",
               "local", "nil", "not", "or", "repeat", "return",
               "then", "true", "until", "while"]

--lua's set of chars that form a valid identifier is restricted to alphanumeric characters and underscore
--in order to resemble at least some level of readability of generated names below 'pseudotranslation' is utilized
--this is not failproof, i.e. you can find 2 different identifiers such that after running both of them though this function
--you will get same output. But that is highly unlikely and would be a result of using bad naming conventions
public export
validateIdentifier : String -> String
validateIdentifier str = fastAppend $ validate <$> unpack (validateKeyword str)
  where
    validate : Char -> String
    validate ':' = "_col_"
    validate ';' = "_semicol_"
    validate ',' = "_comma_"
    validate '+' = "_plus_"
    validate '-' = "_minus_"
    validate '*' = "_mult_"
    validate '\\' = "_bslash_"
    validate '/' = "_fslash_"
    validate '=' = "_eq_"
    validate '.' = "_dot_"
    validate '?' = "_what_"
    validate '|' = "_pipe_"
    validate '&' = "_and_"
    validate '>' = "_gt_"
    validate '<' = "_lt_"
    validate '!' = "_exclam_"
    validate '@' = "_at_"
    validate '$' = "_dollar_"
    validate '%' = "_percent_"
    validate '^' = "_arrow_"
    validate '~' = "_tilde_"
    validate '#' = "_hash_"
    validate ' ' = "_space_"
    validate '(' = "_lpar_"
    validate ')' = "_rpar_"
    validate '[' = "_lbrack_"
    validate ']' = "_rbrack_"
    validate '{' = "_lbrace_"
    validate '}' = "_rbrace_"
    validate '\'' = "_prime_"
    validate '"' = "_quote_"
    validate s with (ord s > 160) --unicode codepoints are above 160
      validate s | False = cast s
      validate s | True = "_uni_" ++ cast (ord s) ++ "_"

    validateKeyword : String -> String
    validateKeyword mbkw = 
       case find (== mbkw) luaKeywords of
          Just kw => "_kw_" ++ kw ++ "_"
          Nothing => mbkw

public export
parseEnvBool : String -> Maybe Bool
parseEnvBool str = 
   case str.toLower of
      "true" => Just True
      "1" => Just True
      "false" => Just False
      "0" => Just False
      _ => Nothing


public export
indent : Nat -> String
indent n = StrExtra.replicate (2 * n) ' '


-- public export
-- escapeString : String -> String
-- escapeString s = concatMap okchar (unpack s)
--   where
--     okchar : Char -> String
--     okchar c = if (c >= ' ') && (c /= '\\') && (c /= '"') && (c /= '\'') && (c <= '~')
--                   then cast c
--                   else case c of
--                             '\0' => "\\0"
--                             '\'' => "\\'"
--                             '"' => "\\\""
--                             '\r' => "\\r"
--                             '\n' => "\\n"
--                             other => "\\u{" ++ asHex (cast {to=Int} c) ++ "}"

export
lift : Maybe (Core a) -> Core (Maybe a)
lift Nothing = pure Nothing
lift (Just x) = x >>= pure . Just

public export
record StrBuffer where
   constructor MkStrBuffer
   get : Buffer
   offset : Int

export 
allocStrBuffer : Int -> Core StrBuffer
allocStrBuffer initialSize = 
   do
      (Just buf) <- coreLift $ newBuffer initialSize
         | _ => throw (UserError "Could not allocate buffer")
      pure (MkStrBuffer buf 0)

export
writeStr : 
      (marker : Type)
   -> {auto buf : Ref marker StrBuffer}
   -> String
   -> Core ()
writeStr marker str = 
   do
      let strlen = stringByteLength str
      strbuf <- get marker
      raw <- ensureSize strbuf.get strbuf.offset strlen
      coreLift $ setString raw strbuf.offset str
      put marker (MkStrBuffer raw (strbuf.offset + strlen))
      pure ()

   where
      ensureSize : Buffer -> Int -> Int -> Core Buffer
      ensureSize buf offset strlen = 
         let bufLen = !(coreLift $ rawSize buf) in
             if offset + strlen > bufLen
                then do
                   (Just buf) <- coreLift $ resizeBuffer buf (max (2 * bufLen) (offset + strlen))
                     | _ => throw (UserError "Could not allocate buffer")
                   pure buf  
             else      
                pure buf

public export
data DeferedStr : Type where
   Nil : DeferedStr
   (::) : Lazy a -> {auto prf : Either (a = String) (a = DeferedStr)} -> DeferedStr -> DeferedStr

export
pure : String -> DeferedStr
pure x = [delay x]

export
traverse_ : (String -> Core b) -> DeferedStr -> Core ()
traverse_ f ((::) x xs {prf = Left Refl}) = do f x; traverse_ f xs
traverse_ f ((::) x xs {prf = Right Refl}) = do traverse_ f x; traverse_ f xs
traverse_ _ [] = pure ()


export
sepBy : List (DeferedStr) -> String -> DeferedStr
sepBy (x :: xs@(_ :: _)) sep = x :: sep :: sepBy xs sep
sepBy (x :: []) _ = [x]
sepBy [] _ = []

--it is actually more general than that, but whatever
export
trimQuotes : String -> String
trimQuotes x = substr 1 (x.length `minus` 2) x


export
forAll : (a -> Bool) -> List a -> Bool
forAll f (x :: xs) = f x && forAll f xs
forAll f [] = True
