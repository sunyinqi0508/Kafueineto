# kafueineto — keep a Mac awake, with optional temporary policy changes.
#
#   make                 build ./kafueineto
#   make test            build and run the native suite (no sudo; read-only
#                        system probes, a per-process com.kafueineto.test.*
#                        defaults domain, and private temporary directories)
#   make test-sanitize   the same suite under AddressSanitizer + UBSan
#   make install         install under $(DESTDIR)$(PREFIX)/bin
#   make clean           remove build products

ifeq ($(origin CXX),default)
CXX = clang++
endif
CXXFLAGS ?= -std=c++17 -O2 -Wall -Wextra -Wpedantic -fblocks
LDLIBS   ?= -framework CoreFoundation -framework IOKit \
            -framework ApplicationServices -framework SystemConfiguration -lutil
PREFIX   ?= /usr/local
DESTDIR  ?=

all: kafueineto

kafueineto: kafueineto.cpp
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) $(LDFLAGS) -o $@ $< $(LDLIBS)

# The harness #includes kafueineto.cpp (renaming its main out of the way
# itself), so it rebuilds whenever either file changes.
test_kafueineto: test_kafueineto.cpp kafueineto.cpp
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) $(LDFLAGS) -o $@ $< $(LDLIBS)

test: test_kafueineto
	./test_kafueineto

test_kafueineto_sanitize: test_kafueineto.cpp kafueineto.cpp
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -O1 -g -fno-omit-frame-pointer \
		-fsanitize=address,undefined $(LDFLAGS) -o $@ $< $(LDLIBS)

test-sanitize: test_kafueineto_sanitize
	./test_kafueineto_sanitize

install: kafueineto
	install -d "$(DESTDIR)$(PREFIX)/bin"
	install -m 755 kafueineto "$(DESTDIR)$(PREFIX)/bin/kafueineto"

clean:
	rm -rf kafueineto test_kafueineto test_kafueineto_sanitize test_kafueineto_sanitize.dSYM

.PHONY: all test test-sanitize install clean
