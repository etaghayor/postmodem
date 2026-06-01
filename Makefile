BUILD=dune build
RUN=dune exec
TEST=dune runtest
CLEAN=dune clean

MAIN=my_project

all:
	$(BUILD)

run:
	$(RUN) bin/main.exe

test:
	$(TEST)

clean:
	$(CLEAN)

utop:
	dune utop

fmt:
	dune fmt

watch:
	dune build --watch