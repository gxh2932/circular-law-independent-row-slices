# Circular-law statement mappings

## Completed full-paper verification (2026-10-10)

All 29 named manuscript results have reviewed targets and checked proofs.
The final two quantitative joint estimates are proved in
[JointSmallestSingularTheorems.lean](CircularLaw/JointSmallestSingularTheorems.lean).

| Manuscript result | Lean target | Checked proof |
| --- | --- | --- |
| `prop:LLY-smallest` | `LLYSmallestSingularTheorem` | `lly_smallest_singular_theorem` |
| `cor:uniform-polynomial` | `UniformPolynomialSmallestSingularTheorem` | `uniform_polynomial_smallest_singular_theorem` |

The proposition supplies three absolute positive constants before the
dimension, degree and shift quantifiers. Its two exponent functions are
equal to `(2*llySourceLoglogRatioConstant+12)*log(log(n))`, independent
of degree and shift. They exceed two and satisfy the literal common
logarithmic upper bound at every admissible dimension. A larger absolute
degree coefficient excludes the finite initial segment of the eventual
source estimates. The model convention `1<=d<=n` implies `n>=2` in its
degree window; this domain is explicit in the Lean target.

The corollary supplies one absolute positive probability coefficient
before quantifying over every `epsilon>0`. The common exponent is
`2*(8*(1+epsilon)/epsilon)+12`, which is greater than two. The estimate
holds for all sufficiently large dimensions, uniformly over every degree
between `log(n)^(1+epsilon)` and `n/2` and every shift in the source
spectral window. Its dimension threshold may depend on epsilon, while
the probability coefficient does not. The user approved the exact
addition of this sufficiently large dimension condition to the printed
corollary, matching its existing proof, and it is applied.

Both targets use `smallestSingularFailureSum`: the actual independent
uniform row-slice probability plus the actual independent Bernoulli(d/n)
entry probability, with the non-strict smallest-singular-value events.
The equivalence with the last ordered singular value is proved in
`square_smallest_singular_failure_iff_last`. A fixed existing source
parameter choice supplies all steep and gradual classes, actual retained
norm bounds, finite nets, adjoint and each omitted-row kernel event, and
the fresh-row scalar bounds. No quantitative source estimate remains a
proof hypothesis.

Fourteen final supporting modules add 53 checked theorems, nine definitions
and one parameter structure. The Bernoulli mean-corrected approximation
accounts for its random row sums, including the additional degree term;
the retained action is the actual shifted matrix action. Rare and large
selected-coordinate small-ball bounds retain all other input coefficients,
and exact product marginalization supplies every retained row law.

The approved tensorization correction is applied. The user also approved
[FINAL_STATEMENT_CORRECTIONS.patch](FINAL_STATEMENT_CORRECTIONS.patch),
which replaces the false rounded T2 comparison in the Bernoulli proof
with the checked convergence of the actual minor prefix T. Its precise
floors and ambient normalization are retained. The named Bernoulli
hermitization statement and the main circular-law theorem are unchanged.
The former auxiliary defect is resolved by this proof revision; its
counterexample remains checked as historical review evidence.

Final verification: the full `lake build` passed with 9142 jobs.
`lake env lean -DwarningAsError=true Audit.lean` passed for 12853 project
declarations, including generated helpers, and 6247 named theorems. Only
`propext`, `Classical.choice` and `Quot.sound` are allowed. The audit also
type-checks `main_circular_law_theorem : MainTheorem`. All seven source
coverage integrity tests and the axiom-rejection test passed. The strict
`paper_coverage.py --require-complete` check passed with 29/29 proved,
zero partial, zero statement-only and zero open results; it resolves every
supporting declaration and type-checks every proof against its named
target. All 14 TeX source hashes and all 29 named statement hashes match
the reviewed ledger, and `git diff --check` passes.

The corrected TeX and regenerated PDF are current. The October revision
note and date in `main.tex` change no named mathematical statement; its
source hash is refreshed after review. The final proof status above
supersedes the historical milestone counts below.

## Earlier proof milestones

The following three manuscript conclusions have unconditional checked
proofs in [CircularLawProvedRegimes.lean](CircularLaw/CircularLawProvedRegimes.lean).
These three source statements are unchanged. The separately approved
tensorization correction is recorded below.

| Manuscript result | Lean target | Checked proof |
| --- | --- | --- |
| `thm:main`, `sections/01_intro.tex:33` | `MainTheorem` | `main_circular_law_theorem` |
| `thm:lower-band-circular`, `sections/09_hermitization.tex:388` | `LowerBandCircularLawTheorem` | `lower_band_circular_law_theorem` |
| `prop:superlog-bridge`, `sections/09_hermitization.tex:457` | `SuperlogarithmicCircularLawTheorem` | `superlogarithmic_circular_law_theorem` |

`MainTheorem` has one existential real constant `C > 0`, followed by every
natural-valued degree sequence with the eventual lower bound
`C*log(n) <= d(n)` and `d(n)/n -> 0`. The lower-band target similarly
has one existential constant **before** quantifying over every
`0 < sigma < 1`; its constant is independent of sigma. Its eventual
degree assumptions are exactly
`C*log(n) <= d(n) <= log(n)^(1+sigma)`. The superlogarithmic target
quantifies over every `epsilon > 0` and every sparse degree sequence
with eventual lower bound `log(n)^(1+epsilon) <= d(n)`.

All three conclusions use `CircularConvergence`, defined by convergence
to zero of the actual uniform row-slice-law probability of every positive
bounded-Lipschitz deviation. `RowSliceMatrix n d` is the tuple of `n`
supports of cardinality `d`; its uniform law is proved to be the
independent product of uniform row laws. The matrix entries are their
zero-one indicators. `empiricalSpectralMeasure` counts characteristic
roots with algebraic multiplicity. `normalizedMatrix` scales the actual
slice matrix by `1/sqrt(d*(1-d/n))`, and `circularMeasure` is the uniform
area probability measure on the complex unit disk.

The degree assumptions eventually give `0 < d(n) < n`, nonempty row
slices, and a positive variance scale. Totalized definitions in small
dimensions or at impossible degrees do not change these limiting claims.
All bounds used in the proofs are eventual; changing finitely many
dimensions does not change convergence.

The proof supplies the actual row-slice minimum limits at both cutoffs,
the actual intermediate singular-value theorem in the lower band, the
regularized row-replacement comparison, and both logarithmic tails.
Bernoulli negative-log uniform integrability removes its prefix ridge,
and its extended full-log limit proves that determinant-zero probability
tends to zero. Determinant interlacing, cancellation of the common degree
normalization, the checked Bernoulli circular potential, direct
hermitization, and variance-normalization transfer give both regimes.
Completed degree sequences and the exact two-filter assembly prove the
main target.

This proof route does not require a quantitative Bernoulli minimum bound
at the common ridge threshold. The separate manuscript conclusions
`prop:LLY-smallest` and `cor:uniform-polynomial` still require their
literal quantitative joint estimates and remain open. The reviewed
rounded auxiliary comparison `eq:SSS-T-upper` is not used. The literal
tensorization lemma is now proved after the approved correction below.
These outstanding obligations prevent full-paper completion even though
the circular-law conclusions are proved.

## Verification of this milestone

On 2026-10-10, the full `lake build` passed with 9097 jobs. The project
axiom audit passed for 12361 declarations, including 6059 named theorems,
and explicitly type-checked `main_circular_law_theorem : MainTheorem`.
Only the standard Lean/mathlib foundations `propext`, `Classical.choice`
and `Quot.sound` are permitted by the audit.

All seven coverage integrity tests and the axiom-rejection regression
test passed. The strict full-paper completion check type-checked the
current mappings and correctly failed at 26/29, with two open results
and one partial result. All 14 manuscript source hashes match the ledger;
the TeX sources are unchanged. `git diff --check` passed.

## Bernoulli quantitative reduction

`BernoulliNonAlmostMinimumBound.lean` now proves the fresh-row scalar
and row-distance estimates for the actual independent-entry law at
`p=d/n`, with `0<d` and `2*d<=n`. The chosen unit normal depends only on
the other rows, and the exact disjoint entry-block law fixes that normal
while averaging the fresh row. The scalar input is the proved
`C_B/sqrt(delta*d)` bound. Its center includes the actual diagonal shift.

The actual smallest-value failure at `(rho/sqrt(n))*rho/sqrt(n)` is at
most `kappa+(C_B/sqrt(delta*d)+eta)/delta` if `kappa` bounds the
almost-constant square-adjoint failure and `eta` bounds every actual
leave-one-out almost-constant kernel failure. These two Bernoulli
probabilities are explicit hypotheses; they are not discharged by this
reduction. Consequently neither named quantitative joint result is
promoted, and coverage remains 26/29.

The full build now passes with 9101 jobs. The updated axiom audit passes
for 12406 declarations, including 6076 named theorems, and checks the
main theorem. All seven coverage integrity tests and the axiom-rejection
regression test pass. The strict completion check type-checks all mappings and
correctly reports the two open results and one partial result. All 14
manuscript source hashes are unchanged.

## Bernoulli gradual estimates and remaining steep estimates

The next milestone adds 42 checked theorems and 15 definitions in nine
modules, from `FiniteProductEventUpperTail.lean` through
`BernoulliLLYAlmostReduction.lean`. The actual Bernoulli product law now
supplies the retained-row load event, row-degree lower tail, surviving-row
count and action, and the gradual almost-constant retained norm bound.
Both the square-adjoint gradual failure and each omitted-row gradual
kernel failure have checked probability bounds
`E = n*exp(-d/200) + exp(-(rowLoadRate/4)*n)` under their explicit finite
geometry, entropy and shift assumptions.

`bernoulli_smallest_probability_of_lly_steep_bounds` splits the previous
almost-constant inputs into gradual and steep classes. Its resulting
bound is `kappa + E + (C_B/sqrt(delta*d) + eta + E)/delta`, where `kappa`
and `eta` still bound the actual steep adjoint and omitted-row kernel
events. Those steep estimates, their eventual source-parameter assembly,
and the literal quantitative exponent requirements remain outstanding.
The two quantitative manuscript mappings include these new supporting
declarations but remain open; no conditional reduction is counted as a
proof of either source conclusion.

On 2026-10-10, the full build passed with 9110 jobs. The current axiom
audit passed for 12490 declarations, including 6118 named theorems, and
checked `main_circular_law_theorem : MainTheorem`. The strict completion
check again type-checked the mappings and reported 26/29 proved, two
open and one partial. All seven coverage integrity tests and the
axiom-rejection regression test passed. All 14 manuscript hashes remain
unchanged, and `git diff --check` passed.

## Bernoulli first steep class at the source parameters

Eight additional modules, from `FiniteProductEventLowerTail.lean` through
`BernoulliFirstSourceReduction.lean`, add 32 checked theorems and ten
definitions. Exact Bernoulli selected-coordinate patterns have witness
probability `|L|*(d/n)*(1-d/n)^(|J|-1)`. Restriction to retained entry
blocks supplies their actual independent row law. The arbitrary finite
product lower tail, eligible-row count and finite disjoint-pair entropy
prove the uniform first-class witness estimate.

The actual row-degree upper failure is at most
`n*exp(-(2*log(2)-1)*d)`. On its complement, a six-degree coordinate jump
and all unique witnesses yield retained norm at least
`sqrt(d)/(4*llyFirstSteepNormConstant)`. Both actual first-class retained
failure and every omitted-row kernel failure have checked finite bounds.
At the literal source ceiling rank, square-root stride, scale and radius,
their failure probabilities are eventually at most `2*n^(-A)` above an
explicit absolute logarithmic degree coefficient. The rank-one class is
empty; this branch also covers the dense degrees where the small-set
witness budget need not hold.

The source-parameter splits now supply this first-class term in the
square-adjoint and omitted-row steep events. Actual adjoint invariance
preserves the conjugated shift. Only the almost-constant second and third
steep classes remain as steep probability inputs. Their bounds, the
complete Bernoulli quantitative source assembly and the literal joint
exponent requirements remain outstanding. The named quantitative results
remain open and coverage remains 26/29.

On 2026-10-10, the full build passed with 9118 jobs. The axiom audit
passed for 12601 declarations, including 6150 named theorems, and checked
the main theorem. The strict completion check type-checked the mappings
and correctly reported two open results and one partial result. All 14
manuscript hashes remain unchanged, and `git diff --check` passed. All
seven coverage integrity tests and the axiom-rejection regression test
passed.

## Approved tensorization correction (2026-10-10)

The user approved and the exact `TENSORIZATION_CORRECTION.patch` was applied
to `sections/02_preliminaries.tex`. The event threshold now has coefficient
one, and the probability constant is explicitly positive. The checked
`tensorization_source_lemma : TensorizationSourceLemma` matches the corrected
source, with `C=4*exp(1)` and all deterministic shifts and nonnegative radii.
Only this approved manuscript file changed; the statement and full source
hash ledger are refreshed. Named coverage is 27 proved, two open and no
partial results out of 29. The two quantitative joint minimum bounds
still prevent full-paper completion.

## Actual centered Bernoulli norm milestone (2026-10-10)

The actual centered Bernoulli operator now has a checked norm bound
`bernoulliComplexNormConstant(A)*sqrt(d)` outside probability `n^(-A)`
for `A>=0`, `n>=2`, `0<d<=n`, and `(A+3)*log(n)<=9*d`. The same event
controls every retained row set simultaneously. Actual Bernoulli
logarithmic edge tails, finite set entropy, both degree caps at `9*d`,
signed centered product moments, two full lattice nets, and the complete
heavy estimate including the centering term supply this proof.
Ten modules from `BernoulliSubsetPoissonTail` through `BernoulliRetainedNorm`
add 44 checked theorems and 12 definitions. The later steep-class
small-ball/net exclusions and the two quantitative joint conclusions
remain open. Named coverage is 27/29 after the approved tensorization
correction.

Verification of this milestone: the full `lake build` passed with 9128
jobs. `lake env lean Audit.lean` audited 12706 project declarations,
including generated helpers, and 6194 named theorems using only the
allowed Lean/mathlib foundations. It also checked the unconditional
`main_circular_law_theorem : MainTheorem`. The strict full-paper check
type-checked every claimed supporting declaration and every proved target
mapping, then correctly reported 27/29 proved, two open, no partial and
no statement-only results. The axiom-audit rejection test passed. All 14
manuscript-file hashes and all 29 named-statement hashes match the reviewed
ledger. The only changed TeX file is the exact approved tensorization
correction; `git diff --check` passed.

All seven coverage integrity tests also passed. Together with the one
axiom-audit rejection test, all eight required integrity tests passed.
Full-paper completion remains unmet solely in the named-result gate
because the two quantitative joint conclusions are open.
