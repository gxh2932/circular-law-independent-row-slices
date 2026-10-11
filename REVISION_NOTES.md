# October 10, 2026 revision

The manuscript and accompanying Lean 4 formalization now have checked proofs
for all 29 named results, including the circular-law theorem at sufficiently
large logarithmic degree, both degree regimes, and both quantitative joint
smallest-singular-value estimates. The main theorem still requires one
sufficiently large absolute constant C; this revision does not optimize it.

## Manuscript corrections

1. **Tensorization lemma (`lem:tensorization`).** Require the probability
   constant to be positive and remove that constant from the squared-radius
   event threshold. The corrected bound has event
   `sum |xi_i|^2 <= tau^2*t^2*K` and probability at most `(C*A*tau^2)^K`.
   [The exact correction and rationale](formalization/TENSORIZATION_CORRECTION.md)
   are retained with the patch.
2. **Superlogarithmic corollary (`cor:uniform-polynomial`).** State explicitly
   that the estimate holds for all sufficiently large n, as used by its
   proof. The probability coefficient is absolute and independent of epsilon;
   the dimension threshold and polynomial exponent may depend on epsilon.
3. **Bernoulli hermitization (`prop:Bernoulli-hermitization`).** Replace the
   false deterministic comparison for a rounded auxiliary prefix T2 with
   direct convergence of the actual minor prefix T. The replacement retains
   the exact floors and ambient normalization. The proposition's conclusion
   and the main theorem are unchanged.
   [The final corrections and rationale](formalization/FINAL_STATEMENT_CORRECTIONS.md)
   include the corresponding patch and links to the checked counterexample.

The compiled PDF is regenerated from the corrected TeX sources and carries
the October revision date. The publication build uses Tectonic 0.17.0;
all 69 pages are rendered for layout review, with the corrected pages
inspected at full reading resolution.

## Formal verification

The project uses Lean 4.28.0 and mathlib v4.28.0 with exact dependency commits
in [lake-manifest.json](formalization/lake-manifest.json). The
[coverage ledger](formalization/paper-coverage.json) maps every named result
to its target proposition and proof. The
[statement review](formalization/CIRCULAR_LAW_STATEMENT_REVIEW.md) records
the correspondence with the manuscript, including its actual matrix laws,
variance normalization, and quantifier order.

Validation includes the full `lake build`, a transitive axiom audit of every
project declaration, strict 29/29 manuscript coverage, seven coverage-integrity
tests, and one axiom-rejection test. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed; admitted proofs and additional mathematical axioms
fail the audit. Source hashes guard subsequent manuscript edits, while
matching the written statements to their Lean targets remains a mathematical
review obligation.

[GitHub Actions](.github/workflows/lean.yml) runs these checks on proposed
changes to the formalization and manuscript. See the
[build instructions](formalization/README.md#build-and-audit) to reproduce them.

The existing Zenodo DOI identifies the earlier deposited version. This note
describes the October GitHub revision; it does not claim a new Zenodo deposit
or peer review.
