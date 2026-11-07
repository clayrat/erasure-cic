# Porting log

Every definition or proof taken from another project is recorded here: source
repository, commit, paths, license and the changes made. Ported proofs are
re-checked by this project's build.

## Dependencies

| Dependency | Where | Pinned commit | Use |
|---|---|---|---|
| [elim-inductive-types](https://github.com/clayrat/elim-inductive-types) | `vendor/elim-inductive-types` (git submodule) | `5ffaed3` on the branch `cic`, after `lecture-7` = `a822b8c` | Declarations, classification, the generator of eliminators and the compiler of lecture 7, built under the prefix `IndTypes` without its `Tests.v`. Edited on its branch `cic`: the level of a declaration becomes a sort, fields are checked by sort, `elim_class` and the declarations of stage 2. |
| [pts-dependent-types](https://github.com/clayrat/pts-dependent-types) | `vendor/elim-inductive-types/vendor/pts-dependent-types` (the submodule nested in elim-inductive-types; not a submodule of this repository) | `1e61d9c` on the branch `cic`, after `lecture-7` = `fd7f98a` | The kernel, built under the prefix `DepTypes` with the modules elim-inductive-types lists. Edited on its branch `cic`: Prop, `Case`, `Fix` and the guard. Of its contracts only `PTS/Contracts.v` is built here; its `Contracts.v` of lecture 6 needs the PCF translation and strictness-pcf. |

## Ported files

None yet.

## Adapted proofs and code

| Here | Source | Commit | Changes |
|---|---|---|---|
| `Makefile`, `_CoqProject`, `.gitignore` | elim-inductive-types, the same files | `a822b8c` | the kernel's and the declarations' modules listed from the nested paths; no extraction or reference targets yet |
