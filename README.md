# Exact Decomposition Branching

This repository provides supplementary material on the paper *Exact Decomposition Branching exploiting Lattices* by K. Halbig, T. Oertel and D. Weninger.

## Installation

To use our code first download and build [exact SCIP][2] with its dependencies *GMP*, *Boost*, and *MPFR*.
Apply the Git patch *bugfix.patch* to *exact SCIP* beforehand to circumvent an unfixed memory bug.

Build *exact Decomposition Branching* using *cmake*:
```
mkdir release
cd release
cmake .. -DSCIP_DIR=path-to-scip-dir/release
make
```

## Usage

In order to use *exact Decomposition Branching*, you need an instance file (for example, in LP or MPS format) as well as a corresponding decomposition file (DEC format). For using the enhanced version utilizising Delta-regularity, you need an additional .meta file.
See also section *Test sets*.

Using *exact Decomposition Branching* in a Linux-based terminal, you can type for example

```
./deltaDB 3600 1 100 path-to-instance.lp path-to-decomposition.dec
```
to use the original version with an epsilon of 1/100 and a time limit of 3600 seconds, and
```
./deltaDB 3600 1 100 path-to-instance.lp path-to-decomposition.dec path-to-meta.meta
```
to use the enhanced version with Delta and a time limit of 3600 seconds.

## Test sets

In the paper we use two different test sets. One contains multi-item single-level lotsizing problems (MI-SL), and the other contains capacitated facility location problems (CFL).
The instances of both test sets inclusive their decomposition files and a suitable .meta file containing the corresponding Delta is in subfolder *instances*.

## How to cite

If you use code or data of this repository in your research, please consider citing the following paper:

> K. Halbig, T. Oertel and D. Weninger (2024).
> Exact Decomposition Branching exploiting Lattices.

Or, using the following BibTeX entry:

```bibtex
@misc{Halbig_ExactDecBranch_2024,
	author = {Halbig, Katrin and Oertel, Timm and Weninger, Dieter},
	title = {Exact Decomposition Branching exploiting Lattices},
	year = {2024}
}
```

[2]: https://github.com/scipopt/scip/tree/exact-rational

