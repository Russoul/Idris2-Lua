# idris2-lua
Lua backend for Idris 2

## Precautions
- This this WIP, expect bugs or undocumented behavior. If you find yourself struggling to install or use the backend
  please file an issue, I will try to resolve it as fast as possible.

## Requirements
- Install `Idris 2` and `Idris 2 API`, see https://github.com/idris-lang/Idris2/blob/master/INSTALL.md for instructions
- Target Lua versions: 5.1, 5.2, 5.3, 5.4 (not tested, but planned), Luajit
- Depends on [lua-utf8](https://github.com/starwing/luautf8.git), [lua-bigint](https://github.com/JorjBauer/lua-bigint.git),
  [lfs](https://keplerproject.github.io/luafilesystem/manual.html) and [vstruct](https://github.com/ToxicFrog/vstruct)
- Also the backend can be used in compatibility mode: create a global variable `NoRequire` and set it to `true` before you compile to Lua.
  Above libraries won't be required to run your code after that, but you won't be able to use their functionality though.
  This means `Integer`, some file IO, buffers and possibly other things won't work (You will have to pass `--no-prelude` to Idris,
  as `prelude` uses at least `Integer`)
  
  
  All libraries can be installed via [*luarocks*](https://luarocks.org):
  
  `luarocks install luautf8 && luarocks install bigint`

  `luarocks install luafilesystem && luarocks install vstruct`
## Installation
 - `make all && make install`

### Status
 - Backend can build Idris 2 itself into one single Lua executable (source) file approximately 7M lines long 
	(with no indents and one extra new line between logical parts).
 - I do my best to keep performance resonable, lua has many limitations concerning
   local variables and nested structures like if-then-else statements
   leading to some design choises that may decrease performance and limit what lua runtime can do to optimize code execution.
	Suggestions are welcome !
 - Idris 2 running on lua can build `Prelude`, quite slow though. Yet binaries generated this way are digitally not the same as those built by Idris's Scheme backend 	
	I have not yet tested their validity. But the only fact that it can do that brings hope :)
 - Major `chez` tests taken from the official repository under `tests/chez` run successfully, but not all !
 - I still do not have a proper testing system ... Think its time to write some more tests
 - Their is an issue with Lua 5.1 that leads to overflows, will look into this.

### Structure and How-Tos
 - The backend consists of an executable file (when compiled) and one lua file that implements primitive functionally required by Idris
   and provides implementations to some foreign interfaces, like File IO and Buffers, defined in Idris with `%foreign`
 - Backend needs to know what version of Lua you target as there are incompatibilities:	
   Define `LuaVersion` global varible with a value of `5.1`, `5.2`, `5.3` or `5.4`??
 - If you want to run generated code from REPL, define `LuaExe` which is the name of lua executable (which should be in `PATH`) of the target version.
   If the variable is undefined, the backend will default to `lua`.


### Good to know
 - Lua 5.1 and Lua 5.2 do not support 64 bit integers !
   Best precision you can get is 52 bits
	Also, if you use Buffers maximum precision is 48 bits !
	Disregarding the Lua version ! This is planned to be fixed moving to native buffers
 - Bits8, Bits16, Bits32, Bits64 are not yet implemented	

### Tests - TODO

