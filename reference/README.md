# Native OCaml reference

Hand-written, readable OCaml versions of erasure and its target evaluator,
as in the `reference/` directories of the kernel and of the declarations,
compared with the Rocq extract by a differential test on complete answers.
They run on the kernel's native reference,
`vendor/elim-inductive-types/vendor/pts-dependent-types/reference/pts_native.ml`:
its signatures, weak-head reduction, and its checker's `infer` in a context
taken as checked (`infer_open_answer`), which erasure asks for the types
of subterms, with `infer_spine` for the types of the prefixes of an
application at once (`infer_spine_open_answer`); both without the trace,
which erasure drops.

`eval_erased_native.ml` follows `theories/Erasure/Target.v`: the erased
terms, the erased signature (declarations with the shape of their fields and
their kind of elimination, instances, definitions) and the evaluator, weak
and by value: □ applied is □, a match on □ is stuck, a `fix` unfolds with its
`k + 1` arguments whatever they are, an eliminator computes by the kind of
its declaration.

`erase_native.ml` follows `theories/Erasure/Erase.v`: the decision (an arity,
or a type whose sort is Prop, found from its weak-head form), the walk with
known types, the singleton and empty matches on propositions, the refusal of
eliminations a category forbids and the demonstration of BypassElim, and the
erasure of signatures, oldest entry first; running out of fuel is
`UndecidedAt` with its stage.

`diff.ml`, with the conversions of `conversions_erased.ml` and of the
kernel's `extracted.ml`, compares both implementations on erasure of terms
and signatures (every fuel from 0 up, for `UndecidedAt`), on the target
evaluator (values, stuck terms, running out of fuel, positions of arguments)
and on the guard of every `fix` of the lecture, and prints the kinds of
answers it met. Agreement on these inputs is evidence, not a proof of
equivalence.

```sh
make test   # from the root: the extract, then this test
```
