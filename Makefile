run:
	cabal run
test: 
	cabal v2-test --test-show-details=direct
.PHONY: test run