#ifdef __cplusplus
   #include "lua.hpp"
#else
   #include "lua.h"
   #include "lualib.h"
   #include "lauxlib.h"
#endif
   #include <stdio.h>

#ifdef __cplusplus
extern "C"{
#endif

#define tofilep(L)      ((FILE **)luaL_checkudata(L, 1, LUA_FILEHANDLE))
static FILE *tofile (lua_State *L) {
   FILE **f = tofilep(L);
   if (*f == NULL)
      luaL_error(L, "attempt to use a closed file");
   return *f;
}

//non-blocking EOF check
static int c_eof (lua_State *L){
   FILE *file = tofile(L);
   int r = feof(file);
   lua_pushinteger(L, r);
   return 1;
}

static const struct luaL_Reg lib [] = {
   {"feof", c_eof},
   {NULL, NULL}
};

int luaopen_lua_native (lua_State *L){
#if LUA_VERSION_NUM == 501    
   luaL_register(L, "idris2-lua-native", lib);
#else    
   luaL_newlib(L, lib);
#endif    
   return 1;
}

#ifdef __cplusplus
}
#endif
