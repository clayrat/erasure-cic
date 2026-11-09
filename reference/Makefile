OCAMLC ?= ocamlc
KERNEL := ../vendor/elim-inductive-types/vendor/pts-dependent-types/reference
GENERATED := ../extraction/generated

.PHONY: all test clean
all: test

# The native erasure and target evaluator run on the kernel's native
# reference; only this test compiles them together with the extract, to
# compare their complete answers (diff.ml) through the conversions of
# conversions_erased.ml and of the kernel's extracted.ml.
#
# The extract and the kernel's files are copied into _build and compiled
# there as they are.  The files here are compiled where they are, so that
# errors point at them, into _build, with every warning an error except
# fragile matches (4), record patterns without [_] (9), type-directed
# disambiguation (40-42, 44, 45) and missing interfaces (70).
EXTERNAL := deptypes.mli deptypes.ml pts_native.mli pts_native.ml extracted.ml
NATIVE := eval_erased_native.ml erase_native.ml
TESTS := conversions_erased.ml diff.ml
WARNINGS := -w +A-4-9-40-41-42-44-45-70 -warn-error +A
OBJECTS := $(addprefix _build/,$(patsubst %.ml,%.cmo,$(filter %.ml,$(EXTERNAL) $(NATIVE) $(TESTS))))

test:
	$(MAKE) -C ../extraction extract
	mkdir -p _build
	cp $(GENERATED)/deptypes.ml $(GENERATED)/deptypes.mli _build/
	cp $(addprefix $(KERNEL)/,$(filter-out deptypes.%,$(EXTERNAL))) _build/
	cd _build && $(OCAMLC) -w -a -c $(EXTERNAL)
	for f in $(NATIVE) $(TESTS); do $(OCAMLC) $(WARNINGS) -I _build -c -o _build/$${f%.*} $$f || exit 1; done
	$(OCAMLC) $(OBJECTS) -o _build/diff
	_build/diff

clean:
	rm -rf _build
