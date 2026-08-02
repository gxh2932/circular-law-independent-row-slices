# The circular law for independent row slices down to logarithmic degree

**Griffin P. Hurt**

Email: [gh7775@rit.edu](mailto:gh7775@rit.edu)

This repository contains the source and compiled PDF of the preprint
*The circular law for independent row slices down to logarithmic degree*.

> **Status:** Preprint, revised July 2026. This manuscript has not been peer reviewed.

## Abstract

Let \(M_n\) be an \(n \times n\) random \(0\)-\(1\) matrix with independent rows, each uniform over vectors having exactly \(d\) ones. We prove that the empirical spectral distribution of
\[
\frac{M_n}{\sqrt{d(1-d/n)}}
\]
converges in probability to the circular law whenever \(C_*\log n \leq d\) and \(d=o(n)\), for an absolute constant \(C_*>0\).

## Files

- [`paper.pdf`](paper.pdf): compiled manuscript
- [`main.tex`](main.tex): main LaTeX file
- [`sections/`](sections): section and bibliography source files
- [`CITATION.cff`](CITATION.cff): citation metadata for GitHub

## Build

The manuscript uses no external figures or nonstandard style files. Build it with:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## Citation

Use the **Cite this repository** menu on GitHub or the metadata in [`CITATION.cff`](CITATION.cff). A DOI or arXiv identifier will be added when one becomes available.

## Copyright

Copyright © 2026 Griffin P. Hurt. All rights reserved. See [`COPYRIGHT.md`](COPYRIGHT.md).
