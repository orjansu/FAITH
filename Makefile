.PHONY : all clean testLaws testProof laws

haskell := $(wildcard src/*.hs)

gen/AbsSie.hs : src/Sie.cf
	bnfc --makefile --outputdir=gen/ src/Sie.cf
	make --directory=gen

sie : gen/AbsSie.hs $(haskell)
	stack build --copy-bins --local-bin-path="."

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
