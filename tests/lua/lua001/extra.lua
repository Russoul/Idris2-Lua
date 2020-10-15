module = {}

local inspect = require('inspect')

function module.apply(f, ...)
   return f(...)
end

local function printListH(list)
   if list.tag == "0" then
      return ""
   elseif list.tag == "1" and list.arg2.tag == "0" then
      return inspect(list.arg1)
   else
      return inspect(list.arg1) .. " " .. printListH(list.arg2)
   end
end


function module.printList(list)
   return '[' .. printListH(list) .. ']'
end

-- converts HVect to lua's dictionary
function module.hVectToDict(hv, dict)
   if hv.tag == "0" then
      return dict
   else
      dict[hv.arg1.arg1] = hv.arg1.arg2
      return module.hVectToDict(hv.arg2, dict)
   end
end

return module
