package = "idris2-lua"
version = "scm-0"

source = {
  url = "git://github.com/russoul/idris2-lua"
}

description = {
  summary = "Support module for Lua backend of Idris 2",
  detailed = [[
   Defines functions that serve as a library for Lua backend of Idris 2
  ]],
  homepage = "http://github.com/russoul/idris2-lua",
  license = "MIT",
}

dependencies = {
  "lua >= 5.1"
}

build = {
  type = "builtin",
  modules = {
    ["idris2-lua"] = "idris2-lua.lua",
	 ["idris2-lua_native"] = "lib.c"
  }
}
