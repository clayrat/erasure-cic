(** * Contracts of lecture 8: erasure of CIC

    The contracts of the kernel (acceptance of [Case], [Fix] and the guard)
    and of the declarations (sorts of elimination) stay in the contracts
    files of their own branches [cic]; this file re-exports them and adds
    the contract of erasure.  Of the kernel only PTS/Contracts.v is
    imported: its Contracts.v of lecture 6 needs the PCF translation and
    strictness-pcf, which this project does not build. *)

From DepTypes.PTS Require Export Contracts.
From IndTypes Require Export Contracts.
