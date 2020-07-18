# idris2-lua
Lua backend for Idris 2

## Requirements
- Install `Idris 2` and `Idris 2 API`, see https://github.com/idris-lang/Idris2/blob/master/INSTALL.md for instructions
- Lua 5.3 is a minimum requirement
- Depends on [lua-utf8](https://github.com/starwing/luautf8.git) and [lua-bigint](https://github.com/JorjBauer/lua-bigint.git)
  packages
  
  Both can be installed via *luarocks*:
  
  `luarocks install luautf8 && luarocks install bigint`
## Installation
 - `make all && make install`
### Tests - TODO

try running an example `Test.idr` in `test` directory,
the name of the executable file is `idris2-lua`
