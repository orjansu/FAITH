.PHONY : all clean testLaws testProof laws

# Default goal.

all : src/Sie.cf
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
