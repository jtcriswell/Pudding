Pudding
=======

KCoFI Pudding: The formal proofs for the KCoFI system

Introduction
============
This is the code for KCoFI Pudding: the formal semantics and control-flow
integrity proofs for the KCoFI system.  This is an enhanced version of the
code found in Appendix B of John Criswell's dissertation.  Specifically, it
contains some proofs for the Virtual Ghost system as well as some incomplete
theorems for proving a tighter control-flow integrity theorem for KCoFI
(namely theorems cfisafe2 and Transcfisafe2).

The primary theorems are in SVAOS.v and Multi.v.

License
=======
The license for the code is in LICENSE.TXT.

Build Instructions
==================

To build the proofs, you must have Coq 8.3pl5 installed (later versions may
work but haven't been tested).  To build the proofs (i.e., to mechanically
verify them with Coq), type "make."  The "-j" option can be used to
compile files in parallel.
