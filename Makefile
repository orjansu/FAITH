.PHONY : all clean testLaws testProof laws

mainfiles := $(wildcard src/*.hs)
typeChecking := $(wildcard src/typeChecking/*.hs)
proofChecking := $(wildcard src/proofChecking/*.hs)
prettyPrinting := $(wildcard src/prettyPrinting/*.hs)
types := $(wildcard src/types/*.hs)

all : sie

gen/AbsSie.hs : src/Sie.cf
	bnfc --makefile --outputdir=gen/ src/Sie.cf
	make --directory=gen

sie : gen/AbsSie.hs gen/AbsLNL.hs $(mainfiles) $(typeChecking) $(proofChecking) $(prettyPrinting) $(types)
	stack build --copy-bins --local-bin-path="."

testLaws : proofFiles/laws/miniLaws.sie gen/TestSie
	./gen/TestSieLaws < proofFiles/laws/miniLaws.sie

testProof :
	./gen/TestSie < proofFiles/proofs/miniProof.sie

gen/AbsSieLaws.hs : src/SieLaws.cf
	bnfc --makefile --outputdir=gen/ src/SieLaws.cf
	make --directory=gen

gen/AbsLNL.hs : src/prettyPrinting/LNL.cf
	bnfc --makefile --outputdir=gen/ src/prettyPrinting/LNL.cf
	make --directory=gen

clean :
	-rm gen/*
