.PHONY : all clean testLaws testProof laws

mainfiles := $(wildcard src/*.hs)
prettyPrinting := $(wildcard src/prettyPrinting/*.hs)
proofChecking := $(wildcard src/proofChecking/*.hs)
typeChecking := $(wildcard src/typeChecking/*.hs)
types := $(wildcard src/types/*.hs)
util := $(wildcard src/util/*.hs)
stackFiles := sie.cabal stack.yaml stack.yaml.lock

all : sie

gen/AbsSie.hs : src/Sie.cf $(stackFiles)
	stack exec bnfc -- --makefile --outputdir=gen/ src/Sie.cf
	stack exec make -- --directory=gen

sie : gen/AbsSie.hs gen/AbsLNL.hs $(mainfiles) $(typeChecking) $(proofChecking) $(prettyPrinting) $(types) $(stackFiles)
	stack build --copy-bins --local-bin-path="."

testLaws : proofFiles/laws/miniLaws.sie gen/TestSie
	./gen/TestSieLaws < proofFiles/laws/miniLaws.sie

testProof :
	./gen/TestSie < proofFiles/proofs/miniProof.sie

gen/AbsSieLaws.hs : src/SieLaws.cf $(stackFiles)
	stack exec bnfc -- --makefile --outputdir=gen/ src/SieLaws.cf
	stack exec make -- --directory=gen

gen/AbsLNL.hs : src/prettyPrinting/LNL.cf $(stackFiles)
	stack exec bnfc -- --makefile --outputdir=gen/ src/prettyPrinting/LNL.cf
	stack exec make -- --directory=gen

clean :
	-rm gen/*
