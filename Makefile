DEBUG ?= 0
ifeq ($(DEBUG), 0)
        CXXFLAGS +=-DNDEBUG -O3 -g
else ifeq ($(DEBUG), 2)
        CXXFLAGS +=-DNDEBUG -O3
else
        CXXFLAGS +=-DDEBUG -O0 -g
endif

all: a244493

a244493: a244493.cpp
	g++ $(CXXFLAGS) -o a244493 a244493.cpp

clean:
	rm -f a244493
