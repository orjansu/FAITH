.PHONY : all clean testLaws testProof laws proof

# Default goal.

all : src/Main.hs
	bnfc --makefile --outputdir=gen/ src/Sie.cf
	make --directory=gen
	stack build --copy-bins --local-bin-path="."

proof : src/Sie.cf
	bnfc --makefile --outputdir=gen/ src/Sie.cf
	make --directory=gen
	./gen/TestSie < proofFiles/proofs/miniProof.sie

testLaws : proofFiles/laws/miniLaws.sie gen/TestSie
	./gen/TestSieLaws < proofFiles/laws/miniLaws.sie

testProof :
	./gen/TestSie < proofFiles/proofs/miniProof.sie

laws : src/SieLaws.cf
	bnfc --makefile --outputdir=gen/ src/SieLaws.cf
	make --directory=gen
	./gen/TestSieLaws < proofFiles/laws/miniLaws.sie


clean :
	-rm gen/*
