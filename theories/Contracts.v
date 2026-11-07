(** * Contracts of lecture 8: erasure of CIC

    The contracts of the kernel (acceptance of [Case], [Fix] and the guard)
    and of the declarations (sorts of elimination) stay in the [Contracts.v]
    of their own branches [cic]; this file refers to them and adds the
    contract of erasure.

    The kernel's [Contracts.v] needs its PCF translation and the
    strictness-pcf submodule, which this project does not build, so only
    the contracts of the declarations are imported for now. *)

From IndTypes Require Contracts.
