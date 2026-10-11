# The circular law for independent row slices down to logarithmic degree

**Griffin P. Hurt**

Email: [gh7775@rit.edu](mailto:gh7775@rit.edu)

This repository contains the source and compiled PDF of the preprint
*The circular law for independent row slices down to logarithmic degree*.

> **Status:** Preprint, revised October 10, 2026. This manuscript has not been peer reviewed.

**Earlier deposited version DOI:** [10.5281/zenodo.21752784](https://doi.org/10.5281/zenodo.21752784)

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
- [`formalization/`](formalization/): Lean proofs and statement mappings
- [`REVISION_NOTES.md`](REVISION_NOTES.md): October corrections and verification
- [`CITATION.cff`](CITATION.cff): citation metadata for the deposited version

## Build

The manuscript uses no external figures or nonstandard style files. Build it with:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
cp main.pdf paper.pdf
```

## Lean formalization

[The Lean 4/mathlib development](formalization/) proves **all 29 named
manuscript results**, including the main circular-law theorem, both degree
regimes, and both quantitative joint minimum estimates. It uses the actual
independent row-slice and Bernoulli laws and the paper's variance normalization.

The main proof is
[`main_circular_law_theorem`](formalization/CircularLaw/CircularLawProvedRegimes.lean).
The [coverage ledger](formalization/paper-coverage.json) and
[statement review](formalization/CIRCULAR_LAW_STATEMENT_REVIEW.md) map the
written claims to their formal targets and proofs.

The full build, transitive axiom audit, strict completion check, and eight
integrity tests pass locally. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. [GitHub Actions](.github/workflows/lean.yml)
runs these checks for manuscript and formalization changes. Follow the
[build and audit instructions](formalization/README.md#build-and-audit)
to reproduce them with the pinned Lean 4.28.0/mathlib v4.28.0 dependencies.

[The October revision note](REVISION_NOTES.md) explains the three manuscript
corrections found during formalization. The compiled PDF matches the corrected
source. Matching each written statement to its Lean target remains a
mathematical review obligation in addition to the machine checks.

## Citation

Use the **Cite this repository** menu on GitHub or
[`CITATION.cff`](CITATION.cff) for the deposited preprint. DOI
[10.5281/zenodo.21752784](https://doi.org/10.5281/zenodo.21752784) identifies
that earlier deposited version. For the October GitHub revision, also record
the repository commit or tag. This update does not create a new Zenodo deposit.

## Copyright

Copyright © 2026 Griffin P. Hurt. All rights reserved. See [`COPYRIGHT.md`](COPYRIGHT.md).
