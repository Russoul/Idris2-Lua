--package.path = package.path .. ";./bigint/?.lua"
--package.path = package.path .. ";./luautf8/?.lua"
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

function System_prim__getArgs()
  return idris__getArgsImpl(1)	
end

function idris__bigint_div(x, y)
  local res, _ = bigint.divide(bigint.new(x), bigint.new(y))
  return res
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
