include config.mk

# Idris 2 executable we're building
NAME = idris2-lua
TARGETDIR = build/exec
TARGET = ${TARGETDIR}/${NAME}
IDRIS2 = idris2
IPKG = idris2-lua.ipkg

MAJOR=0
MINOR=3
PATCH=0


export IDRIS2_VERSION := ${MAJOR}.${MINOR}.${PATCH}

ifeq ($(OS), windows)
	# This produces D:/../.. style paths
	IDRIS2_PREFIX := $(shell cygpath -m ${PREFIX})
	IDRIS2_CURDIR := $(shell cygpath -m ${CURDIR})
	SEP := ;
else
	IDRIS2_PREFIX := ${PREFIX}
	IDRIS2_CURDIR := ${CURDIR}
	SEP := :
endif


.PHONY: all idris2-lua-exec ${TARGET} clean-tests clean check-env test

all: ${TARGET} test

idris2-lua-exec: ${TARGET}

${TARGET}:
	${IDRIS2} --build ${IPKG}

clean-tests:
	$(RM) -r tests/build

clean: clean-tests
	$(RM) -r build
	$(RM) support/lua/*.so
	$(RM) support/lua/*.o

install: install-idris2-lua install-support

install-idris2-lua:
	mkdir -p ${PREFIX}/bin/
	install ${TARGET} ${PREFIX}/bin
ifeq ($(OS), windows)
	-install ${TARGET}.cmd ${PREFIX}/bin
endif
	mkdir -p ${PREFIX}/bin/${NAME}_app
	install ${TARGETDIR}/${NAME}_app/* ${PREFIX}/bin/${NAME}_app

install-support: check-env
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/support/lua
	cd support/lua; \
	luarocks make --lua-version=$(LuaVersion) --local
	install support/lua/idris2-lua.lua ${PREFIX}/idris2-${IDRIS2_VERSION}/support/lua

test: clean-tests install-support
	make -C tests IDRIS2_LUA=../${TARGET}


check-env:
ifndef LuaVersion
	$(error LuaVersion is undefined)
endif

