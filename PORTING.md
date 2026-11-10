# Porting log

Every definition or proof taken from another project is recorded here: source
repository, commit, paths, license and the changes made. Ported proofs are
re-checked by this project's build.

## Dependencies

| Dependency | Where | Pinned commit | Use |
|---|---|---|---|
| [elim-inductive-types](https://github.com/clayrat/elim-inductive-types) | `vendor/elim-inductive-types` (git submodule) | `373bed8` on the branch `cic`, after `lecture-7` = `a822b8c` | Declarations, classification, the generator of eliminators and the compiler of lecture 7, built under the prefix `IndTypes` without its `Tests.v`. Its branch `cic` upstream carries the edits for this project: the level of a declaration becomes a sort, fields are checked by sort, `elim_class` and the declarations of stage 2; the term traversals and examples following `match` and `fix` of the kernel. |
| [pts-dependent-types](https://github.com/clayrat/pts-dependent-types) | `vendor/elim-inductive-types/vendor/pts-dependent-types` (the submodule nested in elim-inductive-types; not a submodule of this repository) | `460fc38` on the branch `cic`, after `lecture-7` = `fd7f98a` | The kernel, built under the prefix `DepTypes` with the modules elim-inductive-types lists. Its branch `cic` upstream carries the edits for this project: Prop, `Case`, `Fix` and the guard (`PTS/Guard.v`, its soundness in `PTS/GuardSound.v`, the examples in `CIC/GuardExamples.v`); `run_infer_open` in its native reference, for the native erasure here. Of its contracts only `PTS/Contracts.v` is built here; its `Contracts.v` of lecture 6 needs the PCF translation and strictness-pcf. |

## Ported files

None yet.

## Adapted proofs and code

| Here | Source | Commit | Changes |
|---|---|---|---|
| `Makefile`, `_CoqProject`, `.gitignore` | elim-inductive-types, the same files | `a822b8c` | the kernel's and the declarations' modules listed from the nested paths; the targets `extract`, `demo`, `test` and `frame` added at stage 8 |
| `extraction/Extract.v`, `extraction/Makefile`, `extraction/dune`, `extraction/dune-project` | elim-inductive-types, `extraction/` | `373bed8` | the export list extended with the examples of this project and erasure; a second extraction, `universes.ml`, for the milestone of universes; the printers of both submodules copied into `generated/` at build time, unchanged |
| `extraction/main.ml`, `extraction/regress.ml` | elim-inductive-types, `extraction/main.ml` and `regress.ml` | `373bed8` | the helpers `header`, `line` and the conversions by normal order with their redexes followed; the demonstrations and checks are new |
| `reference/Makefile` | elim-inductive-types, `reference/Makefile` | `373bed8` | the native files of erasure and the target; the kernel's `extracted.ml` reused for its conversions |
