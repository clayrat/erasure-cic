# erasure-cic

Executable algorithms for the lecture on CoC, CIC, PCUIC and Prop: a CIC
kernel with primitive `match` and `fix` and a guard checker, then erasure of
types and proofs from checked terms.

## Repositories

The work spans three repositories, each on its branch `cic`; their tag
`lecture-7` is the state the notes of lecture 7 cite.

- [pts-dependent-types](https://github.com/clayrat/pts-dependent-types):
  the kernel (Prop, `Case`, `Fix`, guard).
- [elim-inductive-types](https://github.com/clayrat/elim-inductive-types):
  declarations and sorts of elimination.
- this repository: erasure, the target evaluator, the running example with
  `eq`, universes, contracts and demos.

The only submodule is `vendor/elim-inductive-types`; the kernel is its
nested submodule `vendor/elim-inductive-types/vendor/pts-dependent-types`,
the single copy of it in the build paths. Both submodules are edited in
place on `cic`, and the pins move with their commits.

Until `cic` is pushed, the submodules also have a remote `local` pointing at
the sibling checkouts in `~/work`; `origin` stays on GitHub.

## Build

```sh
git submodule update --init --recursive
make              # the kernel, the declarations, then CIC
make assumptions  # every proved contract is axiom-free
make check
make clean
```

## Status

| Component | Status |
|---|---|
| branches `cic`, tags `lecture-7`, build through the nested submodule | done |
