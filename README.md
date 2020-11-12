# Lua backend for Idris 2

## Requirements & Installation
- Install `Idris 2` and `Idris 2 API`, see https://github.com/idris-lang/Idris2/blob/master/INSTALL.md for instructions
- Target Lua versions: 5.1, 5.2, 5.3, 5.4 (not tested, but planned), LuaJIT
- Depends on [lua-utf8](https://github.com/starwing/luautf8.git), [lua-bigint](https://github.com/JorjBauer/lua-bigint.git),
  [lfs](https://keplerproject.github.io/luafilesystem/manual.html), [vstruct](https://github.com/ToxicFrog/vstruct) and
  [inspect](https://github.com/kikito/inspect.lua) (tests only)



#### All libraries can be installed via [*luarocks*](https://luarocks.org):

  ```
  luarocks install luautf8 && luarocks install bigint
  luarocks install luafilesystem && luarocks install vstruct
  luarocks install inspect
  ```

  Before you proceed, fill in the `LuaVersion` and `LuaExe` environment variables with a desired Lua version and a name of the executable file for that version.

#### Build, test and install:

  `make all && make install`

  Idris 2 REPL preconfigured with `lua` codegen will be available under the name `idris2-lua` located in the same folder as your `idris2` executable.

## Status
 - The project aims to keep performance reasonable, Lua has many limitations, concerning
   local variables and nested structures like if-then-else statements,
   leading to design choices that may decrease performance and limit what the Lua runtime can do to optimize execution.
   Suggestions are welcome !

 - Major `chez` tests taken from the official repository under `tests/chez` run successfully, those which don't are primary FFI or BitXX tests.

### Structure and How-Tos
 - Backend needs to know what version of Lua you target as there are incompatibilities:

   Define a global varible `LuaVersion` with a value: `5.1`, `5.2`, `5.3`
 - If you want to run generated code within the REPL, define `LuaExe` with the name of the Lua executable (which should be in `PATH`) of the target version.
   If the variable is undefined, the backend will default to `lua`.


### Good to know
 - Lua 5.1 and Lua 5.2 do not support 64 bit integers !
   Best precision you can get is 52 bits.
   Also, if you use Buffers maximum precision is 48 bits, disregarding the Lua version !
   This is planned to be fixed moving to native buffers.
 - Bits8, Bits16, Bits32, Bits64 are not yet implemented
