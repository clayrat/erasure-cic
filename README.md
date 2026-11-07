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
| contracts of the kernel (`PTS/Contracts.v`, without the PCF translation) and of the declarations, checked by `make assumptions` | done: 17 proved, axiom-free |
| stage 1: Prop beside the predicative hierarchy, Σ by its own table, the table λC (in the kernel) | done in the kernel's `Configs/` and `CIC/Impredicative.v`, with the native reference and the differential test |
| four tables on one checker | `theories/Examples/Tables.v`: the same terms in ∗ and □ under U⁻, λC, the predicative hierarchy and the hierarchy with Prop |
| the examples of Hirrolot's CoC gist on λC | `theories/Examples/CoCGist.v`: Church numerals and `add` with its equations, pairs, vectors by assumption, `concat` by computing the length, `zip` of different lengths rejected with the gist's error, U⁻ rejecting the context |
| stage 2: declarations in Prop, fields checked by sort, the category of elimination | in the kernel, `Elim D s` named by the sort of the motive and `elim_class` with `allows_elimination` in `PTS/Signature.v`; in the declarations, `rd_sort`, `within`, `elim_class_of` and `RElimSort` in `Elim/Declare.v`, the mode `BypassElim`, and `Data/Logic.v`: `True`, `False`, `eq`, `and`, `AccP` eliminating into Type, `or`, `ex`, `BoolP` into Prop only, a witness in `Type₁`, a proof field in data, two proofs told apart under the bypass; native versions and differential tests in both |
