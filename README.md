# KeY Tool Tutorial, FM 2024

This repository contains the accompanying material and the tool executables for the KeY tutorial given at [Formal Methods 2024](https://www.fm24.polimi.it/).

## About KeY

The [KeY tool](https://www.key-project.org) is a state-of-the-art deductive program verifier for the Java language. Its verification engine is based on a sequent calculus for dynamic logic, realizing forward symbolic execution of the target program, whereby all symbolic paths through a program are explored. Method contracts make verification scalable, because one can prove one method at a time to be correct relative to its contract. KeY combines auto-active and fine-grained proof interaction which is possible both at the level of the verification target and its specification, as well as at the level of proof rules and program logic. This makes KeY well-suited for teaching program verification, but also permits proof debugging at the source code level. The latter made it possible to verify some of the most complex Java code to date with KeY. [The accompanying article](https://www.key-project.org/wp-content/uploads/2024/06/KeYTutorialFM2024-preprint.pdf) provides a self-contained introduction to the working principles and the practical usage of KeY for anyone with basic knowledge of logic and formal methods.

## Material

Video material extening the tutorial can be found [here](https://www.key-project.org/tutorial-fm-2024/).

The accompanying article can be downloaded [here](https://www.key-project.org/wp-content/uploads/2024/06/KeYTutorialFM2024-preprint.pdf).

The current version of KeY, any news and information is available on its homepage [`www.key-project.org`](https://www.key-project.org).

The page at [`www.key-project.org/tutorial-fm-2024`](https://www.key-project.org/tutorial-fm-2024) accompanying this tutorial also covers an interactive video tutorial using the material of this repository.

## This repository

This tutorial repository contains two examples on proving programs correct with KeY:

1. `BinarySearch` – contains a simple example of a binary search implementation looking for an integer value in an array. This is the running example used in the article. It covers an imperative and a recursive implementation.
2. `ArrayList` – contains a straightforward List interface together with two implementations that showcase how data structures can be specified and verified in KeY. The interface defines a few methods (`add`, `get`, `size`, and `find`) typical for lists. A ghost variable `seq` that models the abstract value of the list. An implementation `ArrayList` shows how a random-access implementation can realize these functionalities. The class `LinkedList` (together with `Node`) shows a linked list implementation can be specified and verified. There is a ghost field `footprint` used to model the framing condition using dynamic frames.

Both examples comprise:
* `src`: a directory containing the Java source files, annotated with JML specifications
* `project.key`: A KeY input file describing the settings etc. for the resp. example
* `prove.sh`: A shell script to re-run the verification on the command line.
* `proofs` (ArrayList only): Proofs that require interaction are stored here for loading or replay.

The directory `tools` contains the version of KeY to be used for the tutorial.

## Running the tool

### Interactively

If you want to run KeY interactively, the KeY UI can be started by launching the jar file, e.g., using the command
```
$ java -jar tools/key-2.13.0-exe.jar
```
or using the shell script `startkey.sh` in the toplevel directory which suppresses some log messages.

When the UI opens[^1] you can load a project (via the menu `File > Open`). Choose one of the `project.key` files from the example directories to load one of the two examples. A window opens afterward from which you can choose which contract you would like to verify. For an introduction and tips on how to use the system, see the tutorial notes and videos for details (links at the tutorial page mentioned above).

[^1]: It may be that you have to close the example choice window first.

### Verifying from the command line

In case you want to verify the examples fully automatically from the command line, the repository also contains Linux shell scripts that can do this.
You can use the command
```
$ cd BinarySearch; ./prove.sh
```
for the binary search example and the command
```
$ cd ArrayList; ./prove.sh
```
for the list example. Both commands should w/o errors. The last should be

> "[INFO] Summary for project.key: (successful/ignored/failure) (X/0/0)"

**License: GPL-v2-only**
