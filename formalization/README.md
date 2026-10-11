# Lean formalization of the independent row-slice circular law

**All 29 named manuscript results have checked proofs**, including the main
circular-law theorem, both degree regimes, and both quantitative joint
smallest-singular-value estimates. All required mathematical inputs are proved;
no admitted proof or added mathematical axiom is used. The full build, axiom
audit, strict completion check, and eight integrity tests pass locally.

## License

The Lean sources, verification and audit scripts, and Lean package configuration
are licensed under the [Apache License, Version 2.0](LICENSE). See [NOTICE](NOTICE)
for the exact file scope. Third-party dependencies retain their respective
licenses. The manuscript and its LaTeX sources are separately licensed under
[CC BY 4.0](../LICENSE-MANUSCRIPT). See [COPYRIGHT.md](../COPYRIGHT.md) for the
terms for other repository material.

## Main theorem and models

The main proof is `CircularLaw.main_circular_law_theorem` in
[CircularLawProvedRegimes.lean](CircularLaw/CircularLawProvedRegimes.lean).
It proves that there exists an absolute C > 0 such that, for every natural-valued
degree sequence with eventual `C*log(n) <= d(n)` and `d(n)/n -> 0`, the actual
variance-normalized empirical spectral measure converges in probability to the
uniform unit disk. The proof requires a sufficiently large C; this revision
does not optimize or numerically evaluate the final constant.

The row-slice sample is a tuple of supports of cardinality d, with its law
proved to be the independent product of uniform row laws. Matrix entries are
their zero-one indicators. The normalization is `1/sqrt(d*(1-d/n))`, and the
empirical spectral measure counts characteristic roots with algebraic
multiplicity. Convergence uses actual probabilities of every positive
bounded-Lipschitz deviation.

The quantitative joint proofs are in
[JointSmallestSingularTheorems.lean](CircularLaw/JointSmallestSingularTheorems.lean).
They use the actual independent row-slice and Bernoulli(d/n) laws. The
superlogarithmic corollary has one absolute probability coefficient independent
of epsilon, with the polynomial exponent and eventual dimension threshold
allowed to depend on epsilon.

## Statement coverage and review

[paper-coverage.json](paper-coverage.json) maps all 29 named results to their
Lean target propositions, proof declarations, and supporting declarations.
[CIRCULAR_LAW_STATEMENT_REVIEW.md](CIRCULAR_LAW_STATEMENT_REVIEW.md) reviews the
correspondence, including actual matrix laws, normalization, and quantifier
order. [DEPENDENCIES.md](DEPENDENCIES.md) records the proof inputs and their
construction; its earlier milestones are preserved as development history.

The strict coverage check resolves every listed declaration and type-checks
every completed proof against its target. It also checks hashes of all 14
manuscript TeX sources and all 29 named statements. Source hashes guard later
edits; matching the written statements to their Lean targets remains a
mathematical review obligation.

## Build and audit

Install [Lean through elan](https://lean-lang.org/install/), then run from this
directory. `lean-toolchain` selects Lean 4.28.0; `lake-manifest.json` pins
mathlib v4.28.0 and all dependency commits.

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Audit.lean
python3 scripts/test_paper_coverage.py
python3 scripts/test_axiom_audit.py
python3 scripts/paper_coverage.py --require-complete
```

The full build passes with 9142 jobs. The transitive axiom audit covers 12853
project declarations, including generated helpers, and 6247 named theorems.
It explicitly type-checks the main theorem and permits only `propext`,
`Classical.choice`, and `Quot.sound`. Admitted proofs and additional axioms
fail the audit. Common proof dependencies are traversed once while every
project declaration remains covered.

The seven coverage-integrity tests check the valid ledger and reject altered
sources, missing results, invalid status/target data, and nonexistent Lean
declarations. The axiom-rejection test temporarily denies `Classical.choice`
and checks that the audit rejects that existing transitive dependency. It
introduces no axiom or admitted proof. Strict completion passes with 29/29
proved, zero partial, zero statement-only, and zero open results.

[GitHub Actions](../.github/workflows/lean.yml) runs the full build, axiom audit,
integrity tests, and strict completion check for manuscript and formalization
changes. A module build alone does not satisfy the full-paper requirement.

## Manuscript corrections

The corrected PDF is regenerated from the current TeX sources. The
[October revision note](../REVISION_NOTES.md) explains the approved changes:

- [Tensorization correction](TENSORIZATION_CORRECTION.md): use coefficient one
  in the squared-radius threshold and a positive probability constant.
- [Final statement corrections](FINAL_STATEMENT_CORRECTIONS.md): make the
  superlogarithmic corollary's sufficiently large dimension condition explicit
  and replace the false rounded T2 comparison with checked convergence of the
  actual minor prefix T, retaining its exact floors and ambient normalization.

The main theorem and named Bernoulli hermitization conclusion are unchanged.
The original auxiliary comparison's checked counterexample remains in
[HERMITIZATION_REVIEW.md](HERMITIZATION_REVIEW.md) as review evidence.

[DEVELOPMENT_HISTORY.md](DEVELOPMENT_HISTORY.md) preserves the earlier proof
milestones and detailed supporting-result notes. Its historical progress
counts and compiler limitations are superseded by the completed status here.
