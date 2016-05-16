
CLANGBASE = ../../llvm/build/Debug+Asserts/bin/
CPP = $(CLANGBASE)clang++ 
LLC = $(CLANGBASE)llc
LINK = $(CLANGBASE)llvm-link
CPPFLAGS = -fblocks -I. -I../include -std=c++11 -fno-unwind-tables -fno-use-cxa-atexit -fno-cxx-exceptions
CPPFLAGS += --target=atomicc-unknown-linux-gnu
LLVMFLAGS = -emit-llvm

all:
	$(CPP) -c $(CPPFLAGS) $(LLVMFLAGS) -o connect.bc connect.cpp

clean:
	rm -f *.bc *.o *.ll *.s
