COQC ?= coqc
DUNE ?= dune
ELIM := ../vendor/elim-inductive-types
KERNEL := $(ELIM)/vendor/pts-dependent-types
COQFLAGS := -Q $(KERNEL)/theories DepTypes -Q $(ELIM)/theories IndTypes -Q ../theories CIC

.PHONY: all core extract run test frame clean
all: run

core:
	$(MAKE) -C .. rocq

# Extract.v writes generated/deptypes.ml and generated/universes.ml; the
# printers of the kernel and of the declarations are copied next to them
# unchanged.
extract: core
	mkdir -p generated
	$(COQC) $(COQFLAGS) Extract.v
	cp $(KERNEL)/extraction/pretty.ml $(ELIM)/extraction/pretty_ind.ml generated/

run: extract
	$(DUNE) exec ./main.exe

test: extract
	$(DUNE) test

# The spare frame, outside the demos: Print Acc, g by Acc_rect, and its
# extraction, straight from Rocq.
frame:
	$(COQC) Frame.v
	rm -f Frame.vo Frame.vos Frame.vok Frame.glob .Frame.aux

clean:
	rm -rf generated *.vo *.vos *.vok *.glob .*.aux
	$(DUNE) clean
