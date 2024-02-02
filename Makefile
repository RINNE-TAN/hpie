build:
	cabal build
run: build
	cabal exec hpie
test: 
	cabal v2-test --test-show-details=direct
.PHONY: test run