This is the incone library. "incone" is for "information based continuity". It is basically a coq library for computable analysis, but only for the continuity aspects of it.
To install the library, clone the github repository of your coq-installation, r
un make to build the library.

The incone library has some dependencies: it requires some components of mathcomp, the rlzrs and metric libraries that can also be found on my github account, coquelicot and the Interval library.

Be aware that the incone library is a classical library. I make some efforts to only use axioms if necessary, and the realizers declared as proofs of continuity in this library are so far all axiom-free, but the correctness results use Axioms if necessary (in particular it uses the classic axiomatization of Reals from the standard library).
