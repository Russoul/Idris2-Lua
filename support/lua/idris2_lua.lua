
--idris__luaVersion {51,52,53,54}         --set automatically by compiler
--idris__noRequire  {true,false}

if not idris__noRequire then
	utf8 = require("lua-utf8")
	bigint = require("bigint")
	inspect = require("inspect")
	lfs = require("lfs")
	vstruct = require("vstruct")
end

null = {}

-------------------------------------
---- Cross-Version Compatibility ----      --possible Lua version range is [5.1; 5.4]
-------------------------------------		 --supported features may very between versions
														 --as well as the level of optimisations applied
														 --5.4 is probably out of reach yet, as not all required libraries are updated
														 --if ever will be

function idris__addenv(key, val)
   if idris__luaVersion < 52 then
		local env = getfenv(1)
		env[key] = val
		setfenv(1, env)
	else
      _ENV[key] = val
	end	
end	

function idris__getenv(key)
   if idris__luaVersion < 52 then
	  return getfenv()[key]
   else
	  return _ENV[key]
	end 
end 
														 
local idris__abs = math.abs
local idris__modf = math.modf
function idris__getBit32()
  if idris__luaVersion == 51 then   --idris__luaVersion is autodefined by compiler
     return require('bit32')        --bit32 lib is required on lua 5.1
  elseif idris__luaVersion == 52 then
	  return bit32                   --builtin on lua 5.2
  else
     return null                     --lua 5.3 adds native bitwise ops
  end	                              --in this case bit32 won't be used by Idris 2
end

function idris__getToInteger()      --behaviour of math.tointeger of lua 5.3 (returns null on float)
  if idris__luaVersion < 53 then
	  return function (x)
        local int, frac = idris__modf(x)
		  if frac ~= 0.0 then
			  return null
		  else
			  return int
		  end	  
	  end
  else
	  return math.tointeger
  end
end 

function idris__getReadLineString()
  if idris__luaVersion <= 52 then
	  return "*l"
  else
	  return "l"
  end	  
end 

bit32 = idris__getBit32()
idris__tointeger = idris__getToInteger()
idris__readl = idris__getReadLineString()

local function idris__signum(x)
  if x > 0 then
     return 1
  elseif x < 0 then
     return -1
  else
     return 0
  end
end

local function idris__div(x, m)
   local sx = signum(x)
   return (x - sx * (x * sx % idris__abs(m))) / m
end


---------------------------------
---------- Basic stuff ----------
---------------------------------

--used in SchemeCall
function idris__string (list)
	if list.tag == "0" then
		return ""
	else
	   local c = list.arg2
		local other = idris__string(list.arg3)
		return c .. other
	end	
end

idris__addenv("idris__string-append", function(strs)
	return idris__string(strs)
end)


function idris__mkPtr(val)
	if val then return {deref=val} else return null end
end


function PrimIO_prim__nullAnyPtr(ptr)
	if ptr == null then
		return 1
	else
		return 0
	end	
end	

function Prelude_IO_prim__getString(ptr)
	return ptr.deref
end

function Prelude_IO_prim__putChar(char, world)
   io.stdout:write(char)
end

--reads 1 byte (no matter the encoding)
function Prelude_IO_prim__getChar(world)
	local res = io.stdin:read(1)
	if res then
		return res
	else
		return ""
	end	
end

function Prelude_IO_prim__putStr(str, world)
  io.stdout:write(str)
end	

--trims new line
function Prelude_IO_prim__getStr(world)
  local res = io.stdin:read(idris__readl)
  if res then
	  return res
  else
	  return ""
  end	  
end

function System_prim_system(cmd)
  local success, typ, code = os.execute(cmd)
  return code
end	

--------------------  LFS -----------------------------------
idris__last_file_err = -1

function System_Directory_prim_changeDir(d)
	if lfs.chdir(d) then
		return 0 --std lua int is 64bit
	else
		return 1
	end	
end	

function System_Directory_prim_currentDir()
	local cwd = lfs.currentdir()
	return idris__mkPtr(cwd)
end	

function System_Directory_prim_createDir(d)
	local ok, res, errno = pcall(lfs.mkdir, d)
	if ok then
		return 0
	else
		idris__last_file_err = errno
		return 1
	end	
end	

function System_Directory_prim_removeDir(d)
   local ok, res, errno = pcall(lfs.rmdir, d)
	if ok then
		return 0
	else
		idris__last_file_err = errno
		return 1
	end	
end	

function System_Directory_prim_openDir(d)
   local ok, iter, dir = pcall(lfs.dir, d)
	if ok then
		return idris__mkPtr(dir)
	else
		return null 
	end	
end


function System_Directory_prim_closeDir(ptr)
   local ok, res = pcall(function() return ptr.deref:close() end)
	--returns nothing
end

function System_Directory_prim_dirEntry(ptr)
   local ok, res, err, code = pcall(function() return ptr.deref:next() end)
	--if err then print("err " .. err) end
	--if code then print("code " .. code) end
	if ok then
		return idris__mkPtr(res) --returns dir name (String)
	else
		idris__last_file_err = code
		return null
	end	
end	

function System_Directory_prim_fileErrno()
	return idris__last_file_err
end	
--------------------------------------------------------


---------------------- FILE IO -------------------------
idris__last_file_error_string = ""
idris__last_file_error_code = 0

function idris__update_file_error(errstr, code)
	if code and code ~= 0 then
		idris__last_file_error_code = code
		idris__last_file_error_string = errstr
	end
end

function System_File_prim__open(name, mode)
   local f, str, code = io.open(name, mode)
	-- print("open " .. name .. " mode " .. mode)
	idris__update_file_error(str, code)
	-- print("handle", f, "err", str, "cwd", lfs.currentdir())
	if f then
		return idris__mkPtr({handle=f, path=name})
	else
		return null
	end	
end

function System_File_prim__close(file)
   --print(inspect(file))
	file.deref.handle:close()
end

function System_File_prim_error(file)
	if file then return 0 else return 1 end
end

function System_File_prim_fileErrno()
	-- print("fileErrno " .. inspect(idris__last_file_error_code))
	return idris__last_file_error_code
end

function idris__readFile(file, ty)
	local line, err, code = file.deref.handle:read(ty)
	idris__update_file_error(err, code)
	-- print("l", line)
	if err then
		return null
   else
      if line then
			return idris__mkPtr(line)
		else	
			return idris__mkPtr("") --nothing to read, return empty string
			                        --Idris behaviour
		end
	end	
end

function System_File_prim__readLine(file)
    
	 local ptr = idris__readFile(file, idris__readl)
	 if ptr then
	     return idris__mkPtr(ptr.deref .. "\n")
	 else
	     return null
	 end	  
end

function System_File_prim__readChars(n, file)
	return idris__readFile(file, n)
end

function System_File_prim__readChar(fle)
	local res = idris__readFile(file, 1)
	if res and res ~= "" then
      return utf8.byte(res.deref)
	else
		return -1
	end
end

function System_File_prim__writeLine(file, line)
	local ok, err, code = file.deref.handle:write(line)
	idris__update_file_error(err, code)
	if ok then return 1 else return 0 end
end

function System_File_prim__eof(file)
	if file.deref.handle:read(0) then return 0 else return 1 end 
end

function System_File_prim__flush(file)
	local ok, err, code = file.deref.handle:flush() --TODO no documentation for file:flush(), does it return error str and code ?
	idris__update_file_error(err, code)
	if ok then return 0 else return 1 end

end

function System_File_prim__removeFile(name)
	local ok, err, code = os.remove(name)
	idris__update_file_error(err, code)
	if ok then return 0 else return code end 
end


function System_File_prim__fileSize(file)
	local pos = file.deref.handle:seek()
	local bytes, err = file.deref.handle:seek("end")
	idris__update_file_error(err, 5) --set error to generic IO (code = 5)
   if bytes then
	   file.deref.handle:seek("set", pos)
	   return bytes
	else
		error("Failed getting file size for " .. file.deref.path)
	end	
end

function System_File_prim__fPoll(file)
   return System_File_prim__fileSize(file)
end

function System_File_prim__fileModifiedTime(file)
	local ok, err, code = lfs.attributes(file.deref.path, "modification")
	idris__update_file_error(err, code)
   if ok then
		return ok
	else
		return 0
	end
end

function System_File_prim__fileStatusTime(file)
	local ok, err, code = lfs.attributes(file.deref.path, "change")
	idris__update_file_error(err, code)
	if ok then
		return ok
	else
		return 0
	end	
end

function System_File_prim__stdin() 
	return idris__mkPtr({handle=io.stdin, path="$stdin"})
end	

function System_File_prim__stdout() 
	return idris__mkPtr({handle=io.stdout, path="$stdout"})
end	

function System_File_prim__stderr() 
	return idris__mkPtr({handle=io.stderr, path="$stderr"})
end	

function System_File_prim__chmod(path, mod)
	local exit, code = os.execute("chmod " .. string.format("%o", mod) .. " " .. path)
	if exit == "exit" then
		return code
	else
	   return -1
	end
end


--------------------------------------------------------

------------------ BUFFER API -------------------------
--TODO better write a wrapper for native C buffer

function Data_Buffer_prim__newBuffer(size)
	return vstruct.cursor("")
end

function Data_Buffer_prim__bufferSize(buf)
	local pos = buf.pos
	local size = buf:seek("end")
	buf:seek("set", pos)
	return size
end

function Data_Buffer_prim__setByte(buf, offset, value)
	local pos = buf.pos
	buf:seek("set", offset)
	vstruct.write("i1", buf, {value})
	buf:seek("set", pos)
end

function Data_Buffer_prim__getByte(buf, offset)
	local pos = buf.pos
	buf:seek("set", offset)
	local byte = vstruct.read("i1", buf)[1]
	buf:seek("set", pos)
	return byte
end

function Data_Buffer_prim__setInt32(buf, offset, value)
	local pos = buf.pos
	buf:seek("set", offset)
	vstruct.write("i4", buf, {value})
	buf:seek("set", pos)
end

function Data_Buffer_prim__getInt32(buf, offset)
	local pos = buf.pos
	buf:seek("set", offset)
	local i32 = idris__tointeger(vstruct.read("i4", buf)[1])
	if not i32 then error("unexpected float when reading Int32") end
	buf:seek("set", pos)
	return i32
end

function Data_Buffer_prim__setInt(buf, offset, value)
	local pos = buf.pos
	buf:seek("set", offset)
	vstruct.write("i6x2", buf, {value})
	buf:seek("set", pos)
end

function Data_Buffer_prim__getInt(buf, offset)             --64bit integer
	local pos = buf.pos
	buf:seek("set", offset)
	local i64 = idris__tointeger(vstruct.read("i6x2", buf)[1])
   if not i64 then error("unexpected float when reading Int64") end
	buf:seek("set", pos)
	return i64
end

function Data_Buffer_prim__setDouble(buf, offset, value)   --64bit float
	local pos = buf.pos
	buf:seek("set", offset)
	vstruct.write("f8", buf, {value})
	buf:seek("set", pos)
end

function Data_Buffer_prim__getDouble(buf, offset)
	local pos = buf.pos
	buf:seek("set", offset)
	local f8 = vstruct.read("f8", buf)[1]
	buf:seek("set", pos)
	return f8
end

function Data_Buffer_prim__setString(buf, offset, value)   --not null-terminated string (in lua strings may contain
	local pos = buf.pos                                     --arbitrary binary data, size is always known beforehand)
	buf:seek("set", offset)
	vstruct.write("s", buf, {value})
	buf:seek("set", pos)
end


--len is raw length (in bytes not in symbol count)
function Data_Buffer_prim__getString(buf, offset, len)
	if len == 0 then return "" end
	local pos = buf.pos
	buf:seek("set", offset)
	--print("buf", buf, "off", offset, "len", len, "size", Data_Buffer_prim__bufferSize(buf))
	local str = vstruct.read("s"..len, buf)
	--print("got", str[1])
	buf:seek("set", pos)
	return str[1]
end

--TODO copy the contents of the first over the second
--that would be faster
--but not supported natively by the library
function Data_Buffer_prim__copyData(bufA, offsetA, len, bufB, offsetB)
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
function Data_Buffer_prim__readBufferData(file, buf, offset, max)
   --print("file path", file.deref.path)
	--print("file where", file.deref.handle:seek())
	--print("max", max)
	local str, err, code = file.deref.handle:read(max)
	--print("err", err)
	--print("read", str)
	local pos = buf.pos
	buf:seek("set", offset)
	--print("buf cur pos", buf:seek())
	vstruct.write("s", buf, {str})
	--print("buf pos after write", buf:seek())
	buf:seek("set", pos)
	--print("read N", #str)
	return #str
end

function Data_Buffer_prim__writeBufferData(file, buf, offset, len)
	local pos = buf.pos
	buf:seek("set", offset)
	local data = vstruct.readvals("s"..len, buf)
	buf:seek("set", pos)
	file.deref.handle:write(data)
	return #data
end

function Data_Buffer_stringByteLength(str)
	return #str
end

----------------------------------------------------------

function System_prim_getEnv(n)
	return idris__mkPtr(os.getenv(n))
end

function System_prim_exit(code)
	os.exit(code)
end

function idris__getArgsImpl(i)
  if i <= #arg then
    return {tag = "1", arg1 = arg[i], arg2 = idris__getArgsImpl(i + 1)}
  else
    return {tag = "0"}
  end	  
end

function System_prim__getArgs()
  return idris__getArgsImpl(0)	
end

function Prelude_Uninhabited_void(ty, void)
  return "%FromVoid"
end	


--TODO uname may not work correctly if ulimit -Sn <num> is not set to higher number ...
function idris__getOS()
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
				raw_os_name = io.popen('uname -s 2>/dev/null','r'):read(idris__readl)
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

function System_Info_prim__os()
  return idris__getOS()
end	

function PrimIO_prim__schemeCall(ret, name, args, world)
  local f = idris__getenv("idris__" .. name)
  if f then
	  return f(args)
  else
	  error("Could not find lua function: " .. "idris__" .. name .. "\n" .. "All functions used with 'schemeCall' must be prepended with 'idris__' in order to link")
  end	  
end



function idris__ifThenElse(cond, ifTrue, ifFalse)
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
