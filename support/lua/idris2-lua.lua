--idris = {}
--idris.null = {}
--local null = idris.null
--idris.luaVersion {51,52,53,54}         --set automatically by compiler
--idris.noRequire  {true,false}

if not idris.noRequire then
   idrisn = require("idris2-lua_native")
   utf8 = require("lua-utf8")
   bigint = require("bigint")
   lfs = require("lfs")
   vstruct = require("vstruct")
end

idris.error = error
idris.print = print
idris["os.exit"] = os.exit

-------------------------------------
---- Cross-Version Compatibility ----      --possible Lua version range is [5.1; 5.4]
-------------------------------------       --supported features may very between versions
                                           --as well as the level of optimisations applied
                                           --5.4 is probably out of reach yet, as not all required libraries are updated
                                           --if ever will be

function idris.addenv(key, val)
   if idris.luaVersion < 52 then
      local env = getfenv(1)
      env[key] = val
      setfenv(1, env)
   else
      _ENV[key] = val
   end   
end   

function idris.getenv(key)
   if idris.luaVersion < 52 then
     return getfenv()[key]
   else
     return _ENV[key]
   end 
end 
                                           
local abs = math.abs
local modf = math.modf
function idris.getBit32()
   if idris.luaVersion == 51 then    --idris.luaVersion is autodefined by compiler
      return require('bit32')        --bit32 lib is required on lua 5.1
   elseif idris.luaVersion == 52 then
      return bit32                   --builtin on lua 5.2
   else
      return null                    --lua 5.3 adds native bitwise ops
   end                               --in this case bit32 won't be used by Idris 2
end

function idris.getToInteger()        --behaviour of math.tointeger of lua 5.3 (returns null on float)
   if idris.luaVersion < 53 then
      return function (x)
         local int, frac = modf(x)
         if frac ~= 0.0 then
            return nil
         else
            return int
         end     
      end
   else
      return math.tointeger
   end
end 

function idris.getReadLineString()
   if idris.luaVersion <= 52 then
      return "*l"
   else
      return "l"
   end     
end 

function idris.getUnpack()
   if idris.luaVersion == 51 then
      return unpack
   else
      return table.unpack
   end     
end 

function idris.getOnCollectAny()
   if idris.luaVersion == 51 then
      return function(ptr, f) error("prim__onCollectAny not implemented for Lua 5.1") end
   else
      return function (ptr, f)
         local t = getmetatable(ptr)
         if not t then t = {} end
         t.__gc = f
         setmetatable(ptr, t)
         return ptr
      end
   end
end
function idris.getOnCollect()
   if idris.luaVersion == 51 then
      return 
         function(ty, ptr, f) error("prim__onCollect not implemented for Lua 5.1") end
   else
      return function (ty, ptr, f)
         local t = getmetatable(ptr)
         if not t then t = {} end
         t.__gc = f
         setmetatable(ptr, t)
         return ptr
      end
   end
end

bit32 = idris.getBit32()
idris.tointeger = idris.getToInteger()
idris.readl = idris.getReadLineString()
idris.unpack = idris.getUnpack()
idris.onCollectAny = idris.getOnCollectAny()

function idris.signum(x)
   if x > 0 then
      return 1
   elseif x < 0 then
      return -1
   else
      return 0
   end
end
local signum = idris.signum

function idris.div(x, m)
   local sx = signum(x)
   return (x - sx * (x * sx % abs(m))) / m
end
local div = idris.div
local min = math.min
local max = math.max

-- function idris.powbi(base, exp)
--    local zero = bigint:new(0)
--      local one = bigint:one(1)
--      local k = one
--      while exp >= one do
--         k = k * base
--         exp = exp - one
--      end
--      return k
-- end   

function bigint.abs(x)
   if x >= bigint:new(0) then
      return bigint:new(x)
   else
      return -x
   end   
end

function bigint.numd2(x)
   local zero = bigint:new(0)
   local n = 0
   local x = x:abs()
   while x > zero do
      n = n + 1
      x = x:shiftright(1)
   end   
   return n
end   

function idris.bandbi(a, b)
   local a = bigint:new(a)
   local b = bigint:new(b)
   local zero = bigint:new(0)
   local one = bigint:new(1)
   local two = bigint:new(2)
   local ca = a:numd2()
   local cb = b:numd2()
   local cmax = max(ca, cb)
   local tp = two ^ cmax
   local sa = 0
   local sb = 0
   if a < zero then
      a = tp + a
      sa = 1
   end   
   if b < zero then
      b = tp + b
      sb = 1
   end
   ca = a:numd2()
   cb = b:numd2()
   cmax = max(ca, cb)
   cmin = min(ca, cb)
   local r = zero
   for i = 1, cmin do
      local ma = a % two
      local mb = b % two
      r = r + one:shiftleft(i - 1) * (ma * mb)
      a = a:shiftright(1)
      b = b:shiftright(1)
   end
   if sa * sb == 0 then
      return r
   else
      return -(tp - r)
   end   
end 

function idris.borbi(a, b)
   local a = bigint:new(a)
   local b = bigint:new(b)
   local zero = bigint:new(0)
   local one = bigint:new(1)
   local two = bigint:new(2)
   local ca = a:numd2()
   local cb = b:numd2()
   local cmax = max(ca, cb)
   local tp = two ^ cmax
   local sa = 0
   local sb = 0
   if a < zero then
      a = tp + a
      sa = 1
   end   
   if b < zero then
      b = tp + b
      sb = 1
   end
   ca = a:numd2()
   cb = b:numd2()
   cmax = max(ca, cb)
   local r = zero
   for i = 1, cmax do
      local ma = a % two
      local mb = b % two
      local mc = zero
      if ma > zero or mb > zero then mc = one end
      r = r + one:shiftleft(i - 1) * mc
      a = a:shiftright(1)
      b = b:shiftright(1)
   end
   if sa == 0 and sb == 0 then
      return r
   else
      return -(tp - r)
   end   
end 

function idris.bxorbi(a, b)
   local a = bigint:new(a)
   local b = bigint:new(b)
   local zero = bigint:new(0)
   local one = bigint:new(1)
   local two = bigint:new(2)
   local ca = a:numd2()
   local cb = b:numd2()
   local cmax = max(ca, cb)
   local tp = two ^ cmax
   local sa = 0
   local sb = 0
   if a < zero then
      a = tp + a
      sa = 1
   end   
   if b < zero then
      b = tp + b
      sb = 1
   end
   ca = a:numd2()
   cb = b:numd2()
   cmax = max(ca, cb)
   local r = zero
   for i = 1, cmax do
      local ma = a % two
      local mb = b % two
      r = r + one:shiftleft(i - 1) * ((ma + mb) % two)
      a = a:shiftright(1)
      b = b:shiftright(1)
   end
   if (sa + sb) % 2 == 0 then
      return r
   else
      return -(tp - r)
   end   
end 

---------------------------------
---------- Basic stuff ----------
---------------------------------

--used in SchemeCall
function idris.stringImpl (list, buffer)
   if list.tag == "0" then
      return table.concat(buffer) --concat all strings at once, only 1 allocation
   else
      local c = list.arg2
      buffer[#buffer + 1] = c
      return idris.stringImpl(list.arg3, buffer) --tail call
   end   
end
idris.string = function(args) return idris.stringImpl(args, {}) end
idris["string-append"] = idris.string

function idris.mkPtr(val)
   if val then return {deref=val} else return null end
end

idris["PrimIO.prim__nullAnyPtr"] = function(ptr)
   if ptr == null then
      return 1
   else
      return 0
   end   
end   

idris["Prelude.IO.prim__onCollectAny"] = idris.onCollectAny
idris["Prelude.IO.prim__onCollect"] = idris.onCollect

idris["Prelude.IO.prim__getString"] = function(ptr)
   return ptr.deref
end

idris["Prelude.IO.prim__putChar"] = function (char, world)
   io.stdout:write(char)
end

--reads 1 byte (no matter the encoding)
idris["Prelude.IO.prim__getChar"] = function(world)
   local res = io.stdin:read(1)
   if res then
      return res
   else
      return ""
   end   
end

idris["Prelude.IO.prim__putStr"] = function(str, world)
   io.stdout:write(str)
end   

--trims new line
idris["Prelude.IO.prim__getStr"] = function(world)
   local res = io.stdin:read(idris.readl)
   if res then
      return res
   else
      return ""
   end     
end

idris["System.prim__system"] = function(cmd)
   local success, typ, code = os.execute(cmd)
   return code
end   

--------------------------------------------------------
----------------------  LFS ----------------------------
--------------------------------------------------------

idris.last_file_err = -1

idris["System.Directory.prim__changeDir"] = function(d)
   if lfs.chdir(d) then
      return 0
   else
      return 1
   end   
end   

idris["System.Directory.prim__currentDir"] = function()
   local cwd, errstr = lfs.currentdir()
   return idris.mkPtr(cwd)
end   

idris["System.Directory.prim__createDir"] = function(d)
   local ok, errmsg = lfs.mkdir(d)
   if ok then
      return 0
   else
      if errmsg == "File exists" then idris.last_file_err = 4 end
      return 1
   end   
end   

idris["System.Directory.prim__removeDir"] = function(d)
   local ok, errmsg, errno = lfs.rmdir(d)
   if ok then
      return 0
   else
      if errno then idris.last_file_err = errno end
      return 1
   end   
end   

idris["System.Directory.prim__openDir"] = function(d)
   local ok, iter, dir = pcall(lfs.dir, d)
   if ok then
      return idris.mkPtr(dir)
   else
      return null 
   end   
end

idris["System.Directory.prim__closeDir"] = function(ptr)
   local ok, res = pcall(function() return ptr.deref:close() end)
   --returns nothing
end

idris["System.Directory.prim__dirEntry"] = function(ptr)
   local ok, res, err, code = pcall(function() return ptr.deref:next() end)
   if ok then
      return idris.mkPtr(res) --returns dir name (String)
   else
      if code then idris.last_file_err = code end
      return null
   end   
end   

idris["System.Directory.prim__fileErrno"] = function()
   return idris.last_file_err
end   

--------------------------------------------------------
---------------------- FILE IO -------------------------
--------------------------------------------------------

idris.last_file_error_string = ""
idris.last_file_error_code = 0

idris["updateFileError"] = function(errstr, code)
   if code and code ~= 0 then
      idris.last_file_error_string = errstr
      idris.last_file_error_code = code
   end
end

idris["System.File.prim__open"] = function(name, mode)
   local f, str, code = io.open(name, mode)
   idris.updateFileError(str, code)
   if f then
      return idris.mkPtr({handle=f, path=name})
   else
      return null
   end   
end

idris["System.File.prim__close"] = function(file)
   file.deref.handle:close()
end

idris["System.File.prim__error"] = function(file)
   if file ~= null then return 0 else return 1 end
end

idris["System.File.prim__fileErrno"] = function ()
   return idris.last_file_error_code
end

function idris.readFile(file, ty)
   local line, err, code = file.deref.handle:read(ty)
   idris.updateFileError(err, code)
   if err then
      return null
   else
      if line then
         return idris.mkPtr(line)
      else   
         return idris.mkPtr("")  --nothing to read, return empty string
                                 --Idris behaviour
      end
   end   
end

idris["System.File.prim__readLine"] = function(file)
   local ptr = idris.readFile(file, idris.readl)
   if ptr ~= null then
      if idris["System.File.prim__eof"](file) ~= 0 then -- no EOF 
         return idris.mkPtr(ptr.deref .. "\n")
      else return idris.mkPtr(ptr.deref) --[[ no EOL in case we hit EOF --]] end
   else
      return null
   end     
end

idris["System.File.prim__readChars"] = function(n, file)
   return idris.readFile(file, n)
end

idris["System.File.prim__readChar"] = function(file)
   local res = idris.readFile(file, 1)
   if res ~= null and res.deref ~= "" then
      return utf8.byte(res.deref)
   else
      return -1
   end
end

idris["System.File.prim__writeLine"] = function(file, line)
   local ok, err, code = file.deref.handle:write(line)
   idris.updateFileError(err, code)
   if ok then return 1 else return 0 end
end

idris["System.File.prim__eof"] = function(file)
   if idrisn.feof(file.deref.handle) == 0 then return 0 --[[ no EOF --]] else return 1 --[[ EOF --]] end 
end

idris["System.File.prim__flush"] = function(file)
   local ok, err, code = file.deref.handle:flush() --TODO no documentation for file:flush(), does it return error str and code ?
   idris.updateFileError(err, code)
   if ok then return 0 else return 1 end
end

idris["System.File.prim__removeFile"] = function(name)
   local ok, err, code = os.remove(name)
   idris.updateFileError(err, code)
   if ok then return 0 else return code end 
end

idris["System.File.prim__fileSize"] = function(file)
   local pos = file.deref.handle:seek()
   local bytes, err = file.deref.handle:seek("end")
   idris.updateFileError(err, 5) --set error to generic IO (code = 5)
   if bytes then
      file.deref.handle:seek("set", pos)
      return bytes
   else
      error("Failed getting file size for " .. file.deref.path)
   end   
end

idris["System.File.prim__fPoll"] = function(file)
   return idris["System.File.prim__fileSize"](file)
end

idris["System.File.prim__fileModifiedTime"] = function(file)
   local ok, err, code = lfs.attributes(file.deref.path, "modification")
   idris.updateFileError(err, code)
   if ok then
      return ok
   else
      return 0
   end
end

idris["System.File.prim__fileStatusTime"] = function(file)
   local ok, err, code = lfs.attributes(file.deref.path, "change")
   idris.updateFileError(err, code)
   if ok then
      return ok
   else
      return 0
   end   
end

idris["System.File.prim__stdin"] = function() 
   return idris.mkPtr({handle=io.stdin, path="$stdin"})
end   

idris["System.File.prim__stdout"] = function() 
   return idris.mkPtr({handle=io.stdout, path="$stdout"})
end   

idris["System.File.prim__stderr"] = function() 
   return idris.mkPtr({handle=io.stderr, path="$stderr"})
end   

idris["System.File.prim__chmod"] = function(path, mod)
   local exit, code = os.execute("chmod " .. string.format("%o", mod) .. " " .. path)
   if exit == "exit" then
      return code
   else
      return -1
   end
end

--------------------------------------------------------
-------------------- BUFFER API ------------------------
--------------------------------------------------------

--TODO better write a wrapper for native C buffer
--at least because vstruct does not support lua's 5.3 64-bit integers
--plus it looks like its impossible to implement overwriting copying using vstruct

idris["Data.Buffer.prim__newBuffer"] = function(size)
   return vstruct.cursor("")
end

idris["Data.Buffer.prim__bufferSize"] = function(buf)
   local pos = buf.pos
   local size = buf:seek("end")
   buf:seek("set", pos)
   return size
end

idris["Data.Buffer.prim__setByte"] = function(buf, offset, value)
   local pos = buf.pos
   buf:seek("set", offset)
   vstruct.write("i1", buf, {value})
   buf:seek("set", pos)
end

idris["Data.Buffer.prim__getByte"] = function(buf, offset)
   local pos = buf.pos
   buf:seek("set", offset)
   local byte = vstruct.read("i1", buf)[1]
   buf:seek("set", pos)
   return byte
end

idris["Data.Buffer.prim__setInt32"] = function(buf, offset, value)
   local pos = buf.pos
   buf:seek("set", offset)
   vstruct.write("i4", buf, {value})
   buf:seek("set", pos)
end

idris["Data.Buffer.prim__getInt32"] = function(buf, offset)
   local pos = buf.pos
   buf:seek("set", offset)
   local i32 = idris.tointeger(vstruct.read("i4", buf)[1])
   if not i32 then error("unexpected float when reading Int32") end
   buf:seek("set", pos)
   return i32
end

idris["Data.Buffer.prim__setInt"] = function(buf, offset, value)
   local pos = buf.pos
   buf:seek("set", offset)
   vstruct.write("i6x2", buf, {value})
   buf:seek("set", pos)
end

idris["Data.Buffer.prim__getInt"] = function(buf, offset)             --64bit integer
   local pos = buf.pos
   buf:seek("set", offset)
   local i64 = idris.tointeger(vstruct.read("i6x2" --[[ vstruct does not support 5.3 integer type, so write 48bits in any case --]], buf)[1])
   if not i64 then error("unexpected float when reading Int64") end
   buf:seek("set", pos)
   return i64
end

idris["Data.Buffer.prim__setDouble"] = function(buf, offset, value)   --64bit float
   local pos = buf.pos
   buf:seek("set", offset)
   vstruct.write("f8", buf, {value})
   buf:seek("set", pos)
end

idris["Data.Buffer.prim__getDouble"] = function(buf, offset)
   local pos = buf.pos
   buf:seek("set", offset)
   local f8 = vstruct.read("f8", buf)[1]
   buf:seek("set", pos)
   return f8
end

idris["Data.Buffer.prim__setString"] = function(buf, offset, value)   --not null-terminated string (in lua strings may contain
   local pos = buf.pos                                                --arbitrary binary data, size is always known beforehand)
   buf:seek("set", offset)
   vstruct.write("s", buf, {value})
   buf:seek("set", pos)
end


--len is raw length (in bytes not in symbol count)
idris["Data.Buffer.prim__getString"] = function(buf, offset, len)
   if len == 0 then return "" end
   local pos = buf.pos
   buf:seek("set", offset)
   local str = vstruct.read("s"..len, buf)
   buf:seek("set", pos)
   return str[1]
end

--TODO copy the contents of the first over the second
--that would be faster but seems to be impossible with vstruct
idris["Data.Buffer.prim__copyData"] = function(bufA, offsetA, len, bufB, offsetB)
   local posA = bufA.pos
   bufA:seek("set", offsetA)
   local data = vstruct.read(len.."*i1", bufA)
   bufA:seek("set", posA)
   local posB = bufB.pos
   bufB:seek("set", offsetB)
   vstruct.write(len.."*i1", bufB, data)
   bufB:seek("set", posB)
end

--offset is 'buf' offset
idris["Data.Buffer.prim__readBufferData"] = function(file, buf, offset, max)
   local str, err, code = file.deref.handle:read(max)
   local pos = buf.pos
   buf:seek("set", offset)
   vstruct.write("s", buf, {str})
   buf:seek("set", pos)
   return #str
end

idris["Data.Buffer.prim__writeBufferData"] = function(file, buf, offset, len)
   local pos = buf.pos
   buf:seek("set", offset)
   local data = vstruct.readvals("s"..len, buf)
   buf:seek("set", pos)
   file.deref.handle:write(data)
   return #data
end

idris["Data.Buffer.stringByteLength"] = function(str)
   return #str
end

-----------------------------------------------------
------------------- Builtin -------------------------
-----------------------------------------------------

idris["System.prim__getEnv"] = function(n)
   return idris.mkPtr(os.getenv(n))
end

idris["System.prim__exit"] = function(code)
   os.exit(code)
end

function idris.getArgsImpl(i)
   if i <= #arg then
      return {tag = "1", arg1 = arg[i], arg2 = idris.getArgsImpl(i + 1)}
   else
      return {tag = "0"}
   end     
end

idris["System.prim__getArgs"] = function()
   return idris.getArgsImpl(0)   
end

idris["Prelude.Uninhabited.void"] = function(ty, void)
   return "%FromVoid"
end   

--TODO uname may not work correctly if ulimit -Sn <num> is not set to higher number ...
function idris.getOS()
   local raw_os_name
   local env_OS = os.getenv('OS')
   if env_OS then
      raw_os_name = env_OS
   else
      -- LuaJIT shortcut
      if jit and jit.os then
         raw_os_name = jit.os
      else
         -- is popen supported?
         local popen_status, popen_result = pcall(io.popen, "")
         if popen_status then
            if popen_result then popen_result:close() end
            -- Unix-based OS
            raw_os_name = io.popen('uname -s'):read(idris.readl)
         end
      end   
     end   
   if not raw_os_name then raw_os_name = "unknown" end
   raw_os_name = raw_os_name:lower()

   local os_patterns = {
      ['windows'] = 'windows',
      ['linux'] = 'linux',
      ['mac'] = 'mac',
      ['darwin'] = 'darwin',
      ['^mingw'] = 'windows',
      ['^cygwin'] = 'windows',
      ['bsd$'] = 'bsd',
      ['SunOS'] = 'solaris',
   }
   

   local os_name = 'unknown'

   for pattern, name in pairs(os_patterns) do
      if raw_os_name:match(pattern) then
         os_name = name
         break
      end
   end
   return os_name
end

idris["System.Info.prim__os"] = function()
   return idris.getOS()
end   

idris["PrimIO.prim__schemeCall"] = function(ret, name, args, world)
   local f = idris[name]
   if f then
      return f(args)
   else
      error("Could not find lua function: " .. "idris." .. name .. "\n" .. 
            "All functions used with 'schemeCall' must be defined in 'idris' table in order to link")
   end  
end

function idris.ifThenElse(cond, ifTrue, ifFalse)
   local r
   if
      cond
   then
      r = ifTrue()
   else
      r = ifFalse()
   end
   return r
end
