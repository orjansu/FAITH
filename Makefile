.PHONY : all clean test laws

# Default goal.

all : src/Sie.cf
	bnfc --makefile --outputdir=gen/ src/Sie.cf
	make --directory=gen
	./gen/TestSie < proofFiles/proofs/miniProof.sie

test : src/miniProof.sie
	./gen/TestSie < src/miniProof.sie

laws : src/SieLaws.cf
	bnfc --makefile --outputdir=gen/ src/SieLaws.cf
	make --directory=gen
	./gen/TestSie < proofFiles/laws/miniLaws.sie


clean :
	-rm gen/*
