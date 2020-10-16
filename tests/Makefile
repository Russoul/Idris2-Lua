INTERACTIVE ?= --interactive

IDRIS2 ?= idris2
IDRIS2_LUA ?= ../build/exec/idris2-lua
.PHONY: testbin test

test:
	$(IDRIS2) --build tests.ipkg && ./build/exec/runtests ../../$(IDRIS2_LUA) $(INTERACTIVE) --only $(only)

clean:
	$(RM) -r build
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
