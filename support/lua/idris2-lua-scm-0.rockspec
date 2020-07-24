package = "idris2-lua"
version = "scm-0"

source = {
  url = "git://github.com/russoul/idris2-lua"
}

description = {
  summary = "Support module for Lua backend of Idris 2",
  detailed = [[
   Defines functions that combined serve as a backend library for Lua backend of Idris 2
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
    idris2_lua = "idris2_lua.lua"
  }
}
