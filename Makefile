README=README.lagda.md
STYLES=css/Agda.css

check:
	agda $(README)

docs:
	agda --html $(README) --css ../$(STYLES)

.PHONY: check docs
