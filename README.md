# KeY Tool Tutorial, FM 2024

This repository contains the necessary tools for the KeY Tool tutorial on the Formal Methods 2024. 

The KeY tool is a state-of-the-art deductive program verifier for the Java language. Its verification engine is based on a sequent calculus for dynamic logic, realizing forward symbolic execution of the target program, whereby all symbolic paths through a program are explored. Method contracts make verification scalable, because one can prove one method at a time to be correct relative to its contract. \KeY combines auto-active and fine-grained proof interaction which is possible both at the level of the verification target and its specification, as well as at the level of proof rules and program logic. This makes \KeY well-suited for teaching program verification, but also permits proof debugging at the source code level. The latter made it possible to verify some of the most complex Java code to date with \KeY. The article provides a self-contained introduction to the working principles and the practical usage of \KeY for anyone with basic knowledge in logic and formal methods.

A video of the tutorial will be provided [here](#).

The content of this tutorial:

* `BinarySearch/src` -- contains the binary examples 
* `ArrayList/src` -- contains the example 

Additionally, we provide in this artifact the proofs for all proof obligations in the sub-folder `*/proofs`. 

We also provide a copy of the current wqorking KeY and version: You can easily use `make`: 

```
$ make start    # to start KeY
```

```
$ make verify_bs # verify binary search
```

```
$ make verify_al # verify the array list 
```


This artifact is monitored by continous integration pipeline.



**License: GPL-v2-only**
