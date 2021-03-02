.PHONY : all clean

# Default goal.

all : src/Sie.cf
	bnfc --makefile --outputdir=gen/ src/Sie.cf
	make --directory=gen
	./gen/TestSie < src/miniProof.sie

.PHONY: test
test : src/miniProof.sie
	./gen/TestSie < src/miniProof.sie

clean :
	-rm gen/*
