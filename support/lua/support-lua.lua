local utf8 = require("lua-utf8")
local bigint = require("bigint")

function Prelude_prim__putStr(str, world)
  io.write(str)
end	

function Prelude_prim__getStr(world)
  return io.read()
end

function idris__getArgsImpl(i)
  if i <= #arg then
    return {tag = "1", t1 = arg[i], t2 = idris__getArgsImpl(i + 1)}
  else
    return {tag = "0"}
  end	  
end

function Prelude_Uninhabited_void(ty, void)
  return "%FromVoid"
end	

function idris__getOS()
	local raw_os_name, raw_arch_name = '', ''

	-- LuaJIT shortcut
	if jit and jit.os and jit.arch then
		raw_os_name = jit.os
		raw_arch_name = jit.arch
	else
		-- is popen supported?
		local popen_status, popen_result = pcall(io.popen, "")
		if popen_status then
			popen_result:close()
			-- Unix-based OS
			raw_os_name = io.popen('uname -s','r'):read('*l')
			raw_arch_name = io.popen('uname -m','r'):read('*l')
		else
			-- Windows
			local env_OS = os.getenv('OS')
			local env_ARCH = os.getenv('PROCESSOR_ARCHITECTURE')
			if env_OS and env_ARCH then
				raw_os_name, raw_arch_name = env_OS, env_ARCH
			end
		end
	end

	raw_os_name = (raw_os_name):lower()
	raw_arch_name = (raw_arch_name):lower()

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
	
	local arch_patterns = {
		['^x86$'] = 'x86',
		['i[%d]86'] = 'x86',
		['amd6'] = 'x86_64',
		['x86_64'] = 'x86_64',
		['Power Macintosh'] = 'powerpc',
		['^arm'] = 'arm',
		['^mips'] = 'mips',
	}

	local os_name, arch_name = 'unknown', 'unknown'

	for pattern, name in pairs(os_patterns) do
		if raw_os_name:match(pattern) then
			os_name = name
			break
		end
	end
	for pattern, name in pairs(arch_patterns) do
		if raw_arch_name:match(pattern) then
			arch_name = name
			break
		end
	end
	return os_name, arch_name
end

function System_Info_prim__os()
  local os, arch = idris__getOS()
  return os
end	

function idris__getArgsList(args)
  if args.tag == "0" then
    return {}
  else
    local other = idris__getArgsList(args.t3)
    if #other == 0 then
      return {args.t2}
    else
      return {args.t2, table.unpack(other)}
    end  
  end  
end  

function PrimIO_prim__schemeCall(ret, name, args, world)
  return {tag = "0", t1 = _G[name](table.unpack(idris__getArgsList(args))), t2 = world}
end

function System_prim__getArgs()
  return idris__getArgsImpl(1)	
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
