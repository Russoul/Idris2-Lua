module LuaCommon


import Core.Core
import Core.Name
import Data.Buffer
import Data.Buffer
import Data.List
import Data.List
import Data.List1
import Data.String.Extra
import Data.String
import Data.Vect
import Data.Zippable

import Libraries.Utils.Hex

infixl 100 |>

||| Flipped tightly bound function application
public export %inline
(|>) : a -> (a -> b) -> b
x |> f = f x

namespace Strings
  FromString (List Char) where
    fromString = fastUnpack

  public export
  record String1 where
    constructor MkString1
    head : Char
    tail : String

  public export
  data NonEmptyString : String -> Type where
    ItIsNonEmptyString : (0 prf : IsJust (strUncons str)) -> NonEmptyString str

  public export
  toString1 : (str : String) -> {auto 0 prf : NonEmptyString str} -> String1
  toString1 str @{ItIsNonEmptyString itIs} with (strUncons str)
   toString1 str @{ItIsNonEmptyString ItIsJust} | Just (x, xs) = MkString1 x xs

  public export
  toList1 : (str : String) -> {auto 0 prf : NonEmptyString str} -> List1 Char
  toList1 str @{ItIsNonEmptyString itIs} with (strUncons str)
   toList1 str @{ItIsNonEmptyString ItIsJust} | Just (x, xs) = x ::: fastUnpack xs

  public export
  ||| Removes all occurances of the literal @lit
  ||| in the string @str
  removeAll :
        (lit : String)
     -> (str : String)
     -> String
  removeAll lit str with (str == "")
     removeAll lit str | False =
        if isPrefixOf lit str
           then removeAll lit (substr (length lit) (length str `minus` length lit) str)
           else case strUncons str of
                     Just (head, rest) => strCons head (removeAll lit rest)
                     Nothing => ""
     removeAll lit str | True = ""

  -- TODO Useful function to add to `base` ?
  ||| Splits the subject string into parts by the delimiter.
  public export
  split : (delim : List1 Char) -> (subject : List Char) -> List1 (List Char)
  split delim subject =
    reverse $ splitHelper delim subject [] []
    where
      splitHelper : List1 Char -> List Char -> List Char -> List (List Char) -> List1 (List Char)
      splitHelper delim [] acc store = (reverse acc) ::: store
      splitHelper delim str@(x :: xs) acc store =
        case isPrefixOf (forget delim) str of
          -- Dropping a non-zero sequence of characters from `str` ensures that `str` is structurally smaller with each successive call
          True => splitHelper delim (assert_smaller str $ drop (length $ forget delim) str) [] (reverse acc :: store)
          False => splitHelper delim xs (x :: acc) store

  public export %inline
  indent : Nat -> String
  indent n = replicate (2 * n) ' '

  public export
  trimLeft : List Char -> List Char
  trimLeft (' ' :: xs) = trimLeft xs
  trimLeft xs = xs

  public export %inline
  trim : List Char -> List Char
  trim = reverse . trimLeft . reverse . trimLeft


public export
data LuaVersion = Lua51 | Lua52 | Lua53 | Lua54


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
           nodots = removeAll "." noprefix
           nodashes = removeAll "-" nodots
           firstTwo = take 2 nodashes
       in
           do int <- parseInteger {a = Int} firstTwo
              fromIndex int


namespace Data.List
  public export
  contains : Eq a => List a -> a -> Bool
  contains [] _ = False
  contains (x :: xs) x' = x == x' || contains xs x

  public export
  group : {n : _} -> List a -> Vect n (a -> Bool) -> Vect n (List a)
  group [] _ = replicate _ []
  group (x :: xs) fs
   = zipWith List.(++) (map (\f => fromMaybe [] (toMaybe (f x) [x])) fs) (group xs fs)


namespace Data.Maybe
  public export %inline
  orElse : (maybe : Maybe a) -> (def : Lazy a) -> a
  orElse = flip fromMaybe

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
  case toLower str of
    "true" => Just True
    "1" => Just True
    "on" => Just True
    "false" => Just False
    "0" => Just False
    "off" => Just False
    _ => Nothing

||| Escape some of the ascii codes, fail on unicode, as
||| not all supported lua versions have unicode escape sequences
public export
escapeStringLua : String -> Maybe String
escapeStringLua s = concat <$> traverse okchar (fastUnpack s)
  where
    okchar : Char -> Maybe String
    okchar c = if (c >= ' ') && (c /= '\\') && (c /= '"') && (c <= '~')
                  then Just (cast c)
                  else case c of
                            '\0' => Just "\\0"
                            '"' => Just "\\\""
                            '\\' => Just "\\\\"
                            '\r' => Just "\\r"
                            '\n' => Just "\\n"
                            _ => Nothing

||| Transforms `x, y, ... w => body` into `function(x) return function(y) ... return function(w) return body end ... end end
public export
curryTransform : (vars : List (List Char)) -> (body : List Char) -> List Char
curryTransform [] body = body
curryTransform (x :: xs) body = "function(" ++ x ++ ") return " ++ curryTransform xs body ++ " end"

export %inline
sequenceMaybe : Maybe (Core a) -> Core (Maybe a)
sequenceMaybe Nothing = pure Nothing
sequenceMaybe (Just x) = x >>= pure . Just

public export
record StrBuffer where
  constructor MkStrBuffer
  get : Buffer
  offset : Int


namespace StrBuffer

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
data DeferredStr : Type where
  Nil : DeferredStr
  (::) : Lazy a
      -> {auto prf : Either (a = String) (a = DeferredStr)}
      -> Lazy DeferredStr
      -> DeferredStr


namespace DeferredStr

  export
  pure : String -> DeferredStr
  pure x = [delay x]

  export
  traverse_ : (String -> Core b) -> DeferredStr -> Core ()
  traverse_ f ((::) x xs {prf = Left Refl}) = do ignore (f x); traverse_ f xs
  traverse_ f ((::) x xs {prf = Right Refl}) = do traverse_ f x; traverse_ f xs
  traverse_ _ [] = pure ()

  export
  sepBy : Lazy (List (DeferredStr)) -> String -> DeferredStr
  sepBy (x :: xs@(_ :: _)) sep = x :: sep :: sepBy xs sep
  sepBy (x :: []) _ = [x]
  sepBy [] _ = []

  export
  (++) : Lazy DeferredStr -> Lazy DeferredStr -> DeferredStr
  [] ++ rhs = rhs
  (x :: xs) ++ rhs = x :: xs ++ rhs

--it is actually more general than that, but whatever
export
trimQuotes : String -> String
trimQuotes x = substr 1 (length x `minus` 2) x

public export %inline
forAll : (a -> Bool) -> List a -> Bool
forAll f xs = foldl (\ac, x => ac && f x) True xs
