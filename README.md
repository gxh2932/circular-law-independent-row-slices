# The circular law for independent row slices down to logarithmic degree

**Griffin P. Hurt**

Email: [gh7775@rit.edu](mailto:gh7775@rit.edu)

The circular law for sparse random matrices with independent row slices at
sufficiently large logarithmic degree, with the manuscript, LaTeX source,
**Lean 4/mathlib proofs**, and reproducible verification.

[**Research page**](https://gxh2932.github.io/circular-law-independent-row-slices/)
· [**Read the PDF**](https://gxh2932.github.io/circular-law-independent-row-slices/paper.pdf)
· [**Lean proofs**](formalization/)
· [**Zenodo v1.1 & source archive**](https://zenodo.org/records/23289935)

> **Status:** Preprint, revised October 10, 2026. This manuscript has not been peer reviewed.

**Current version:** v1.1-preprint · DOI
[10.5281/zenodo.23289935](https://doi.org/10.5281/zenodo.23289935).

## Abstract

Let $M_n$ be an $n \times n$ random zero–one matrix with independent rows, each
uniform over vectors having exactly $d$ ones. We prove that, for an absolute
constant $C_*>0$, the empirical spectral distribution of

$$
\frac{M_n}{\sqrt{d(1-d/n)}}
$$

converges in probability to the circular law whenever $C_*\log n \leq d$ and
$d=o(n)$. This lowers the known $\log^{2+\varepsilon}n$ threshold to sufficiently
large logarithmic degree throughout the sparse range.

The main obstacle is the lack of column regularity, which removes the
aggregate-profile identities available for random regular digraphs. In the
lower polylogarithmic range, we replace those identities by an averaged
multinomial row-profile estimate and combine it with a rectangular right-kernel
analysis to control all but $O(n/d^2)$ of the smallest singular values. A
regularized row-replacement argument then compares logarithmic determinants
with those of an i.i.d. Bernoulli matrix. Above every fixed superlogarithmic
cutoff, the same comparison is combined instead with a uniform polynomial
smallest-singular-value bound. Girko hermitization and the sparse i.i.d. circular
law complete the proof.

## Files

- [`paper.pdf`](paper.pdf): compiled manuscript
- [`main.tex`](main.tex): main LaTeX file
- [`sections/`](sections): section and bibliography source files
- [`formalization/`](formalization/): Lean proofs and statement mappings
- [`REVISION_NOTES.md`](REVISION_NOTES.md): October corrections and verification
- [`CITATION.cff`](CITATION.cff): citation metadata for the deposited version
- [`docs/`](docs/): research page, search metadata, and publishing instructions

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
The main theorem requires one sufficiently large absolute constant C; this
revision does not optimize its value.

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

Hurt, Griffin P. (2026). *The circular law for independent row slices down to
logarithmic degree* (v1.1-preprint). Zenodo.
[doi:10.5281/zenodo.23289935](https://doi.org/10.5281/zenodo.23289935).

Use the **Cite this repository** menu on GitHub or
[`CITATION.cff`](CITATION.cff) for this deposited version. For the evolving Lean
code, also record the repository commit or tag. The
[earlier v1.0 deposit](https://doi.org/10.5281/zenodo.21752784) remains available.

## Copyright

Copyright © 2026 Griffin P. Hurt. All rights reserved. See [`COPYRIGHT.md`](COPYRIGHT.md).
