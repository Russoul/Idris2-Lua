# Lua backend for Idris 2

## Precautions
- This this WIP, expect bugs or undocumented behavior. If you find yourself struggling to install or use the backend
  please file an issue, I will try to resolve it as fast as possible.

## Requirements & Installation
- Install `Idris 2` and `Idris 2 API`, see https://github.com/idris-lang/Idris2/blob/master/INSTALL.md for instructions
- Target Lua versions: 5.1, 5.2, 5.3, 5.4 (not tested, but planned), Luajit
- Depends on [lua-utf8](https://github.com/starwing/luautf8.git), [lua-bigint](https://github.com/JorjBauer/lua-bigint.git),
  [lfs](https://keplerproject.github.io/luafilesystem/manual.html), [vstruct](https://github.com/ToxicFrog/vstruct) and
  [inspect](https://github.com/kikito/inspect.lua) (tests only)

  
  
#### All libraries can be installed via [*luarocks*](https://luarocks.org):
  
  ```
  luarocks install luautf8 && luarocks install bigint
  luarocks install luafilesystem && luarocks install vstruct
  luarocks install inspect
  ```
  
  Before you proceed, fill in `LuaVersion` and `LuaExe` environmental variables with a desired Lua version and a name of the executable file for that version.
  
#### Build, test and install:
  
  `make all && make install`
  
  Idris 2 REPL preconfigured with `lua` codegen will be available under the name `idris2-lua` located in the same folder as your `idris2` executable.
  
## Status
 - Backend can build Idris 2 itself into one single Lua executable (source) 
   file approximately 7M lines long 
   (with no indents and one extra new line between logical parts).
 - The project aims to keep performance reasonable, Lua has many limitations concerning
   local variables and nested structures like if-then-else statements
   leading to design choises that may decrease performance and limit what Lua runtime can do to optimize code execution.
   Suggestions are welcome !
 - Idris 2 running on Lua can build `Prelude`, quite slow though. Yet binaries generated this way are digitally not the same as those built by Idris's Scheme backend.
   Their functionality has not yet been tested. But the only fact that it can do that brings hope :)
 - Major `chez` tests taken from the official repository under `tests/chez` run successfully, but not all !
 - There is an issue with Lua 5.1 that causes stack overflows, it will be looked upon.

### Structure and How-Tos
 - The backend consists of an executable file (when compiled) and one Lua file that implements primitive functionally required by Idris
   and provides implementations of foreign interfaces, like File IO and Buffers, defined in Idris with `%foreign`
 - Backend needs to know what version of Lua you target as there are incompatibilities:

   Define global varible `LuaVersion` with a value of `5.1`, `5.2`, `5.3` or `5.4`??
 - If you want to run generated code from REPL, define `LuaExe` with the name of Lua executable (which should be in `PATH`) of the target version.
   If the variable is undefined, the backend will default to `lua`.


### Good to know
 - Lua 5.1 and Lua 5.2 do not support 64 bit integers !
   Best precision you can get is 52 bits.
   Also, if you use Buffers maximum precision is 48 bits !
   Disregarding the Lua version ! This is planned to be fixed moving to native buffers
 - Bits8, Bits16, Bits32, Bits64 are not yet implemented
 - Also the backend can be used in compatibility mode: create a global variable `NoRequire` and set it to `true` (or `1`) before you compile to Lua.
   Above libraries won't be required to run your code after that, but you won't be able to use their functionality though.
   This means `Integer`, file IO, buffers and possibly other things won't work (You will have to pass `--no-prelude` to Idris,
   as `prelude` uses at least `Integer`)
