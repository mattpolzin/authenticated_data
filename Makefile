INTERACTIVE ?= --interactive

IDRIS := idris2

PACKAGE = idris-auth.ipkg

all: build

.PHONY: build

build:
	$(IDRIS) --build $(PACKAGE)

.PHONY: clean

clean:
	$(IDRIS) --clean $(PACKAGE)

.PHONY: install

install:
	$(IDRIS) --install $(PACKAGE)
	
