# Resolved rounded Bernoulli logarithmic squeeze review

The user approved `FINAL_STATEMENT_CORRECTIONS.patch` on 2026-10-10,
and it is applied. The manuscript proof now uses the checked convergence
of the actual minor prefix T directly. The false rounded T2 formula and
its comparison are removed. The Bernoulli hermitization proposition,
main theorem and all other named conclusions are proved. The final
coverage count is 29/29, and all required verification gates pass.

The detailed counterexample and historical proof milestones below record
why the correction was needed and how the replacement was developed;
their earlier open-result counts are superseded by the current status.
See [FINAL_STATEMENT_CORRECTIONS.md](FINAL_STATEMENT_CORRECTIONS.md) and
[CIRCULAR_LAW_STATEMENT_REVIEW.md](CIRCULAR_LAW_STATEMENT_REVIEW.md).

## Historical review and proof development

The exact displayed comparison `eq:SSS-T-upper` in
[`sections/09_hermitization.tex`](../sections/09_hermitization.tex) needs
integer-rounding review. Its current `T2` formula counts an extra term.
The issue is verified by Lean for an actual sample of the Bernoulli matrix.
No manuscript source has been changed.

Take `n=100`, `epsilon=1/10`, `d=10`, `B=0` and `z=-2`. The source rounding gives

```
m=90, ell=87, a=20, b=90, c=floor((1-3*epsilon)*n)=70.
```

Then `H=B/sqrt(d)-zI=2I`, and its principal minor is `2I` of dimension 90.
Every singular value of both matrices is exactly 2. Thus

```
T  = -(87/100)*log(2),
T2 = -((90-20+1)+(87-70))/100*log(2)
   = -(88/100)*log(2).
```

Since `log(2)>0`, the displayed inequality `T<=T2` fails. This is a
finite, nonsingular example with a nonzero spectral shift. The all-zero
sample has strictly positive probability `(1-p)^(n*n)` for every `p<1`,
including the literal parameter `p=d/n=1/10`.

The checked declarations are:

- `squeeze_rounding_example` checks all five manuscript floors and ceiling.
- `scalar_square_singular_values` checks the actual ordered singular values
  of every scalar identity matrix through its Gram eigenvectors.
- `rounded_minor_log_upper_counterexample` proves failure for `H=2I`.
- `bernoulli_empty_rounded_upper_counterexample` gives that failure for the
  actual normalized shifted Bernoulli sample.
- `bernoulli_empty_counterexample_positive_probability` checks its positive
  probability under the actual `p=d/n` law.

Their sources are [`RoundedMinorLogReview.lean`](CircularLaw/RoundedMinorLogReview.lean),
[`ScalarSquareSingularValues.lean`](CircularLaw/ScalarSquareSingularValues.lean),
and [`BernoulliEmptyMatrix.lean`](CircularLaw/BernoulliEmptyMatrix.lean).

The manuscript cites Fact 9.1 of
[SSS25, arXiv:2310.17600v2](https://arxiv.org/html/2310.17600v2#S9)
for this step. A correction must account for inclusive integer endpoints
and the actual number `n-m` of deleted rows and columns. Possible approaches
are to prove an explicit vanishing rounding error, or to define a compatible
integer comparison using the exact interlacing shift `2*(n-m)`. Neither
corrected probabilistic squeeze has been claimed as proved.

The counterexample establishes a defect in the exact auxiliary comparison.
The full Bernoulli logarithmic convergence assertion and circular-law
theorem remain open proof targets. All named completed-result counts
exclude these targets.

Two other parts of this interface are now checked independently:

- The original second-moment assertion is proved for the actual Bernoulli
  singular-value measure, with expectation at most `2+2*abs(z)^2`.
- Bounded support and the limiting law's linear small-value mass bound imply
  `FiniteLogarithmicIntegral`, including zero mass at zero and integrability
  of both logarithmic parts. The actual Gaussian limiting law, these bounds and its
  circular-potential logarithmic value are now proved at every shift.

Both sides of Hermitian principal-matrix interlacing are also proved, along
with exact singular-value interlacing under row and column deletion.
`MatrixColumnRestriction.lean` identifies the actual erased-coordinate
kernel and its codomain dimension. `ColumnSingularInterlacing.lean` applies
the spectral dimension comparison to this kernel, and
`PrincipalSingularInterlacing.lean` combines both deletions to give the
exact shift `r=2*(n-m)` for an actual square principal minor.

`ExactMinorLogComparison.lean` now proves an integer-compatible finite
upper comparison. Put `k=m-r` and assume `r<=m`, `k<=ell<=m` and `ell>0`.
For positive ambient singular values and positive minor singular values
in the retained prefix, the minor prefix divided by `n` is at most

```
(sum_{j=r}^{m-1} -log(s_j(H))
 + (ell-k)*(-log(s_{ell-1}(H_minor)))) / n.
```

All indices here are zero-based. The ambient interval has exactly `k`
terms, so the total coefficient count is `ell`, regardless of the signs
of their logarithms. This is a checked finite correction proposal. The
remaining truncated-limit and rounding-limit arguments needed for the
probabilistic squeeze have not been proved, and the manuscript formula
has not been replaced.

The exact source floors now have checked dimension limits in
`BernoulliSqueezeRounding.lean`: `m/n->1`, `ell/n->1`, `n/ell->1` and
vanishing removed fractions. For `0<=epsilon<=1`, the compatible base
count `m-2*(n-m)` is at most `ell`. The condition `2*(n-m)<=m` also holds
eventually for nonnegative `epsilon_n->0`.

The retained-prefix lower-bound deduction and convergence for fixed
clipped logarithms are checked in `RetainedPrefixSmallValues.lean`,
`EmpiricalPrefixMeans.lean` and `BernoulliPrefixConvergence.lean`, with weak
convergence and the actual limiting mass bound still explicit inputs.
These steps permit zero singular values in the discarded tail. The slow
choice and the full untruncated `T1` limit are now checked in
`BernoulliSlowPrefixLimit.lean`: from weak convergence and the limiting
mass and support bounds, the actual Bernoulli prefix converges to
`-integral(log,nu)` along a positive nonincreasing `epsilon_n->0`.
Retained-zero probability also tends to zero. The proof uses the checked
Bernoulli second moment, and assumes no empirical full-log convergence.

This closes the `T1` deduction with the actual Gaussian inputs now supplied.
The selector also preserves arbitrary fixed-stage eventual constraints, and
`BernoulliJointPrefixLimit.lean` gives a common choice for `T1` and an
auxiliary fixed-fraction limit.

`BernoulliLogSqueeze.lean` proves full extended-log convergence from the
literal ambient and minor-prefix limits and the actual full-to-minor upper
failure probabilities. `BernoulliSlowLogSqueeze.lean` supplies one common
choice for these estimates directly from fixed-fraction minor limits and
upper estimates whose error vanishes as the fraction tends to zero. Singular
samples are included in the failure events; their probability tends to zero
as part of the deduction. The actual Gaussian inputs and circular-potential identity are now proved.
The full prefix `T1` and the literal minor prefix `T` converge along one
common slow fraction in `BernoulliCommonMinorLogPrefix.lean`. Here `T` is
`eq:SSS-T`, distinct from the displayed `eq:SSS-T2`; the latter convergence
has not been claimed as checked. The full-to-minor upper estimate remains
unproved. `BernoulliMinorUpperReduction.lean` reduces the full logarithmic
limit to that explicit upper estimate. These conditional assembly theorems
do not establish the manuscript's erroneous finite rounded comparison.

`SquareSingularDeterminant.lean` identifies the actual singular-value product
with the absolute determinant and proves the zero-event equivalence.
`BernoulliLogDeterminant.lean` transfers a full empirical log limit to the
normalized log determinant, permitting arbitrary redefinition on singular
samples. The manuscript remains unchanged.

The exposure-process drift dependency is now proved independently:
`HalfIntegerExposureDrift.lean` checks SSS25 Lemma 8.4 with the source
conditional success probability, moving barrier and half-integer heights,
including q=0. `ExposureGoodEventCoupling.lean` checks the coupling that
kills height on nested currently measurable graph-event failures. Actual
Bernoulli graph estimates, the small-dimension projection regime, alternating
row/column process assembly and the full-to-minor upper comparison remain
open. Uniform coordinate-spread basis existence is now checked below.

The kernel-projection row-insertion inequality used in SSS25 Lemma 7.2
is now checked for r<=n, including zero old products, in
`RowAdditionSingularProducts.lean`. The projection is the actual orthogonal
projection onto the kernel of the first r left-singular rows. A nonzero
old product gives dimension m-r, and `LeadingRowKernelGeometry.lean`
checks the next-singular-value near-kernel norm bound. At r=n the kernel
is exactly the full matrix kernel. The interlacing branch and the actual
normalized logarithmic increment are checked in `RowAdditionLogIncrement.lean`.
The projection-small event bounds the logarithmic step-failure event.
Adjoint singular values, reindexing, column insertion and literal last-index
deletion steps are now checked as well. The actual Bernoulli scalar
small-ball bound is proved in `WeightedBernoulliSmallBall.lean` for complex
coefficients and centers. `BernoulliProjectionSmallBall.lean` uses projection
energy and the count of small basis coordinates to bound the actual
projection probability from coordinate spread. `BernoulliExposureSmallBall.lean`
then bounds the actual row and column log-step failure probabilities.
The earlier bounds expose spread-basis and radius hypotheses.
`UniformBasisSpread.lean` now supplies a basis in every nonzero subspace
whose vectors each have at least `h/4096` coordinates of modulus at least
`sqrt(h)/(64*n)`. Its fair-sign moments, Fourier mixing, compactness,
maximization and pair-rotation inputs are all proved.
`BernoulliSubspaceSmallBall.lean` removes the assumed spread basis from
actual projection and row/column log-step probability bounds; positive
dimension and compatible radii remain explicit. The small-dimension graph-spread projection
regime and graph-event probabilities are unproved. These do not
close the full-to-minor upper comparison. The manuscript has not been edited.

`BernoulliLargeProjection.lean` now proves the Bernoulli case of the
large-dimension projection estimate at the exact SSS25 Lemma 6.2 radius.
When `d=n*p>=1` and `h>=n*d^(-1/4)`, the actual shifted projection-small
probability is bounded by `C*(kappa+d^(-1/4))` with an explicit absolute C.
The closed source interface has a Lean proof. `BernoulliLargeExposure.lean`
supplies the actual row/column log-step failure bounds when their scalar
threshold is at most that radius. The small-dimension graph-spread regime,
graph probabilities, threshold instantiation and alternating process
assembly remain open. These proofs do not repair the rounded `T2` comparison.

The deterministic graph coordinate-gap argument is now checked in
`UniqueNeighbourhoodGeometry.lean`, `ShiftedGraphBudgets.lean`,
`UniqueNeighbourhoodAmplification.lean`, `GraphCoordinateGap.lean` and
`GraphNearKernelGap.lean`. The proof uses the actual shifted matrix,
includes embedded diagonal rows in the middle-support count, retains
the literal one-based ranks and source fifth/seventh powers, and proves
both image spread and the resulting near-kernel exclusion of a coordinate
gap. Unique-neighbourhood, heavy-row and column-degree budgets are explicit
hypotheses about actual finite supports. Random graph probabilities,
instantiation of the source thresholds and the alternating
process remain unproved. The growth and conditional projection proofs below do not promote a named
manuscript claim or close the full-to-minor upper comparison.

`GraphGrowthBudget.lean` and `SourceGraphGap.lean` now obtain the middle
support count from the uniform source column-degree condition, using the
literal ceiling growth function and a fixed explicit constant.
`GraphGrowthIteration.lean` proves the first exit bound
`(4*C+2)*log(n/k)^4` for its actual integer recurrence.
`SourceGraphGrowthRange.lean` checks the exact terminal scale
`n*log(log d)/(2*d)` and valid next ranks. `GraphNearKernelIteration.lean`
propagates the actual initial modulus through the entire recurrence under
the uniform graph events and an explicit image-energy threshold.

`GraphSubspaceSmallBall.lean` applies this to the proved initial spread
basis of every suitable nonzero subspace. Its actual Bernoulli projection
bound is `2*C_scalar/sqrt(ceil(u)*p)`, and at the source terminal scale
with `d=n*p` it is at most `4*C_scalar/sqrt(log(log d))`. The uniform
near-kernel energy and projection-radius comparisons are explicit;
the source `eta_r` comparisons have not been discharged. Random graph
event probabilities and the alternating process remain unproved. The full
small-dimension SSS25 projection lemma and full-to-minor comparison are
therefore still open.


The graph-basis argument now includes initial coordinate counts already
beyond the terminal scale. `GraphLeadingKernel.lean` supplies the actual
leading-row kernel's uniform near-kernel estimate from its next singular
scale, including zero scale when every row is retained.
`BernoulliGraphExposure.lean` proves that a failed row or adjoint-column
log step forces that scale below `exp(-N*delta)`. Its actual Bernoulli
failure probability satisfies the terminal graph projection bound under
the graph events and the two explicit threshold energy/radius comparisons.
Thus the exposure interfaces assume no spread basis or uniform near-kernel
estimate. Random graph probabilities, the source threshold comparisons and
alternating process assembly still need proofs. The full-to-minor upper
comparison remains open, the rounded `T2` statement-review issue remains,
and no manuscript text or named-result status has changed.


The source-form scalar threshold comparisons are now proved in the
integer guarded exposure range. `GraphProjectionThreshold.lean` and
`GraphProjectionCost.lean` check the exact radius and logarithmic cost;
`SourceGraphProjectionThreshold.lean` uses `g=N-r<=9*(m-r)` from the
rounded guard to dominate it by the source eighth powers. Raw-matrix
row/adjoint-column failures at both source-form branches are checked.

The normalized projection thresholds are checked separately, retaining
`sqrt(d)`. `NormalizedGraphThreshold.lean` absorbs it by doubling the
explicit small-branch coefficient. `NormalizedLargeProjection.lean` gives
the actual squared-log projection bound with the remaining fraction as
radius coefficient. `NormalizedSourceProjection.lean` combines both
actual leading-kernel projection branches, with error tending to zero
as the fraction shrinks and degree grows. Its actual singular-scale
hypothesis, integer guard and graph budgets remain explicit. The actual
normalized insertion-log transfer is checked below. Random graph
probabilities, accumulated log errors and process assembly remain open.
The full-to-minor upper estimate and rounded `T2` statement-review
issue remain unresolved. Named coverage is still 23/29; no manuscript
text has changed.

Actual rectangular singular values now have checked scalar homogeneity,
including the inserted row index type and zero scalars. The actual
inserted products scale exactly. Their log-prefix corrections require
nonzero products, and positive growth by `sqrt(d)*exp(-N*delta)` supplies
new-product positivity before using the new logarithm.

`NormalizedInsertionLogIncrement.lean` therefore proves the actual
degree-normalized row and column steps. Its failure event includes a zero
new retained product. `NormalizedSourceExposure.lean` applies the checked
source projection bounds after showing that failure forces the next raw
singular scale below the normalized threshold. Both actual Bernoulli
insertion directions now satisfy the combined error bound with the
deterministic graph events and guard explicit. This completes the
normalized log-prefix transfer. The literal accumulated rank-error bound
is checked below; random graph-event probabilities and the adapted
alternating process remain open.
No unrestricted imported projection lemma or named manuscript result is
promoted. Manuscript text and the 23/29 named coverage are unchanged.

The accumulated source-schedule error is now checked for the actual
finite rank sum. `NormalizedLogPowerSums.lean` and `TwoBranchLogSums.lean`
retain the integer cutoff and bound the squared/eighth-power branches.
`SourceNormalizedLogError.lean` gives
`32*sqrt(L/N)+C(K,beta)*log(d)^8*d^(-1/8)` and proves that it tends to zero
along shrinking fractions and growing degrees. The actual rank interval
is reindexed exactly. A sharper linear-in-fraction estimate is not claimed.

`LastIndexDegreeNormalizedSteps.lean` applies the normalized insertion
steps to the manuscript's last-row/last-column views, including positive
new products. Keeping the same rank preserves positivity and decreases
the normalized prefix. `BernoulliMinorUpperProbabilityReduction.lean`
uses one common slow fraction for both proved prefix limits and an upper
estimate with deterministic and probability errors vanishing with that
fraction. The actual upper estimate and adapted process are still open.
No named status or manuscript text has changed.

The actual Bernoulli graph column-degree probability is now checked.
`BernoulliSubsetCountLaplace.lean` and `BernoulliColumnSubsetCounts.lean`
give the exact product-law exponential moment and fixed-set tail.
`ColumnDegreeEntropyBounds.lean` and `BernoulliColumnDegreeBudget.lean`
absorb all subset counts and prove uniform failure probability at most
`N^(-3)` with degree-budget constant eight and effective degree `d=N*p>=1`.

For unit-bounded entries, `HeavyRowsFromColumnDegree.lean` derives the
literal fifth-power-threshold heavy-row budget from the total row mass.
`ColumnDegreeRestriction.lean` retains both budgets under injective row
and column restrictions. `BernoulliGraphDegreeProbability.lean` therefore
proves both budgets for every restriction of the actual square/sparse law
outside the same `N^(-3)` event, when `d>=32` and `0<beta<=1`; the source
range `d>=exp(4)` is included. Unique-neighbourhood expansion probability,
the actual adapted alternating process and the upper comparison remain
open. No named result is promoted; source text and coverage are unchanged.

Adjoint invariance of the actual square/sparse Bernoulli law is now checked
in `BernoulliAdjointLaw.lean`. `BernoulliBidirectionalGraphDegree.lean`
supplies both degree budgets for every restriction of both orientations
outside a single `2*N^(-3)` event for `d>=32` and `0<beta<=1`.

The actual selected row-pattern probabilities and row product law are
checked. `BernoulliUniqueRowLaw.lean`, `BernoulliUniqueCountLaplace.lean`
and `BernoulliUniqueCountStructure.lean` give the actual unique-neighbourhood
mean, exponential moment and lower tails, retaining diagonal zero-pattern
and outside single-one contributions. Independent-row factorization is
proved from the actual entry measure.

`BernoulliUniqueSmallSetFactors.lean` retains the diagonal factor needed
for subset counting. `BernoulliSquareSmallSetExpansion.lean` absorbs that
count and bounds cardinality-ell failure by `exp(-d*ell/16)` in its checked
numerical range. `BernoulliSquareSmallExpansionProbability.lean` proves
uniform actual square expansion for all `|S|>=k>0` with `|S|*p<=1/2`, with
failure at most `2*exp(-d*k/16)` when `d>=exp(64)`.

The rectangular and larger-set expansion inputs are now checked.
At the original ambient degree `d=N*p`, the square-minor and one-column
rectangular small-set failure bounds are `2*exp(-d*k/16)` and
`4*exp(-d*k/16)`, respectively, when at least `3*N/4` rows remain.
The unmatched final column is counted as a separate family, retaining
the exact diagonal row count. For `d>=exp(1024)` and `p<=1/2`, the actual
larger-set mean is at least `N/(4*log(d))`, the source expansion threshold
is at most half that bound, and the subset entropy is absorbed.

`BernoulliSourceUniqueExpansionProbability.lean` proves the full source
budget with failure at most the small-set bound plus
`N*exp(-N/(64*log(d)))`, for at most N columns, seed `k>0` and `0<beta<=1`.
`BernoulliRectangularRestrictionLaw.lean` and
`BernoulliRestrictedUniqueExpansion.lean` transfer the estimates via the
exact coordinate marginal to each specified ambient restriction and
adjoint restriction. Simultaneous exposure graph probabilities and
conditional insertion laws are supplied below. Progressive good events,
adapted process assembly and the full upper estimate remain open. The manuscript and
named coverage are unchanged.


`SourceExposureExpansionSeed.lean` checks the positive deterministic seed
`(N-m)/32768+1` against the actual leading-kernel coordinate count at the
integer barrier. `BlockedExpansionFailureSums.lean` sums the seed errors
without losing a factor N. `SourceExposureUniqueEvents.lean` now supplies
simultaneous unique expansion for every relevant square and one-column
rectangular prefix in both orientations. Combined graph failure is at most
`2*N^(-3)+786444*exp(-d/16)+4*(N+1)*N*exp(-N/(64*log(d)))` for
`d=N*p>=exp(1024)`, `p<=1/2` and `0<beta<=1`.
`SourceExposureGraphFailureRates.lean` proves that this bound, and the
actual simultaneous graph failure probability, tend to zero as degree grows.

`FiniteFreshConditionalExpectation.lean` checks that conditioning fixes
the finite past and averages an independent fresh block.
`BernoulliFreshConditionalExpectation.lean` proves independence and the
exact conditional probabilities for disjoint actual entry blocks.
`BernoulliPrefixFreshLaw.lean` supplies both actual next-row and next-column
laws. `SourceConditionalInsertion.lean` applies the checked normalized
failure bounds in the current prefix sigma-algebra, allowing the retained
rank and shift vector to depend on the exposed entries. Its past event
must imply the explicit positive-product, barrier, fraction and graph
conditions. Progressive graph-event measurability and the adapted retained-rank
construction are now proved below. The concrete conditional drift and
actual full-to-minor upper estimate are proved below.
No named result is promoted, and manuscript source hashes are unchanged.

`BernoulliPrefixFiltration.lean` and `AlternatingPrefixSchedule.lean`
construct the actual nested prefix sigma-algebras and column-then-row
filtration. `SourcePrefixGraphBudgets.lean` instantiates the graph conditions
on each exposed square or one-column rectangle.
`SourceProgressiveGraphEvents.lean` proves that the intersection of these
conditions through the current time is measurable in the current
filtration and nested. Its failure probability is uniformly bounded by
the checked simultaneous graph error, which tends to zero.

`WideBarrierExposureDrift.lean`, `WideBarrierExposureCompletion.lean` and
`WideBarrierGoodEventCoupling.lean` prove an auxiliary drift and killed
process bound at the doubled-height barrier `2*((T-s)/8)`, with terminal
error `16*q^(1/8)` plus good-event failure. The original source drift
lemma remains separately checked. `AlternatingRetainedHeight.lean` checks
the actual doubled modified height, including the full-rank rectangular
case, its growth, successful-step decrease, initial/terminal identities
and strict insertion guard above this wider barrier.

`GreedyPrefixRetainedRank.lean` defines the actual policy on exposed
prefixes and proves its adaptedness, rank validity, monotonicity and
single-step bounds. `RectangularRetainedPrefixMonotonicity.lean` checks
same-rank singular products and log prefixes under simultaneous row and
column restriction. `GreedyPrefixLogControl.lean` proves positive products
at every time and the cumulative actual log bound from an initial positive
product. `GreedyTerminalLogBound.lean` identifies the terminal cost with
the literal source rank sum and bounds it by
`sourceNormalizedLogErrorBound` at the omitted-rank fraction, conditional
on terminal rank N. That error vanishes as the fraction shrinks and degree
grows by the previously checked scalar theorem.

The concrete conditional insertion bounds, matrix identities and height
drift are now proved below, together with a finite terminal-rank and
prefix-log probability bound. Identifying the normalized manuscript
full/minor quantities and discharging their fixed-fraction asymptotic
conditions remain open. The preceding 12 modules add 66 named theorems
and 20 definitions; named coverage stays 23/29. No source statement or
manuscript hash changes.

`BernoulliPrefixInsertionViews.lean` checks the literal square and
one-column rectangular deletion and fresh-vector identities. The fresh
column has no diagonal shift, while the fresh row has the raw shift in
its last coordinate. The adjoint column interface uses the conjugate raw
shift. `BernoulliPrefixNormalizedFailure.lean` identifies the reindexed
insertion failure with actual new-product zero or actual log-step failure.

`SourceGreedyExposureConditions.lean` includes initial-product positivity
in the progressive good event and proves its current measurability,
nesting and failure bound. Actual rank monotonicity bounds the remaining
fraction by its initial value. On the current good event, the actual
positive product, graph budgets and wide height barrier supply every
local insertion condition. `GreedyPrefixRowConditional.lean` and
`GreedyPrefixColumnConditional.lean` instantiate both conditional failure
estimates with the constructed greedy rank.

`AlternatingPrefixInsertionIdentities.lean` transports the actual product
and log across explicit dimension equalities without changing the
ambient sample. `GreedyPrefixStepFailure.lean` checks every schedule step
and proves actual acceptance is the complement of the corresponding
insertion failure. `GreedyExposureHeight.lean` supplies the adaptedness,
initial/growth/terminal identities and proves that a bad height step has
capacity and rejects the increase. `GreedyConditionalDrift.lean` then
proves the actual conditional height drift; it is no longer an assumption.

`GreedyExposureCompletion.lean` applies the checked coupling. Under
`0<N`, `3*N/4<=M<=N`, `r0<=M`, `2*(M-r0)<=N-M`,
`d=N*p>=exp(1024)`, `0<p<=1/2`, `0<beta<=1`,
`(N-r0)/N<=epsilon<=exp(-4)` and `beta<=norm(zRaw)<=d`, terminal rank
failure is at most the initial positive-product failure plus the
simultaneous graph error plus
`16*normalizedSourceProjectionFailureBound(epsilon,d)^(1/8)`.
The actual zero-product or excessive terminal-prefix log event is bounded
by twice the initial failure plus the same graph and drift errors, with
the deterministic `sourceNormalizedLogErrorBound` at `(N-r0)/N`.

`SquareRetainedPrefixIdentities.lean` identifies the square retained log
with the literal singular-value prefix and positive product with absence
of retained zeros. `GreedyPrefixPaperNormalization.lean` checks the raw
shift `z*sqrt(d)`, ambient minor normalization and terminal full logarithm.
`BernoulliGreedyCutoff.lean` retains both source floors and proves the
initial-height and omitted-fraction conditions eventually at every fixed
positive epsilon at most 1/8; the omitted fraction is at most 2*epsilon.
`BernoulliGreedyPaperPrefix.lean` applies the finite probability bound to
the actual normalized full zero-or-log-excess event and proves the initial
retained-zero probability tends to zero using the checked minor weak law.
These four modules add 17 theorems and one definition.

`BernoulliGreedyErrorRates.lean` proves the fixed-fraction error limits
and their vanishing as the cutoff decreases to zero.
`BernoulliGreedyAsymptoticParameters.lean` supplies the actual `p=d/n`,
large-degree and raw-shift conditions eventually.
`BernoulliGreedyMinorUpperLimit.lean` proves the fixed-fraction upper
probability bound and the full Bernoulli logarithmic limit at every fixed
nonzero shift, using the checked common slow choice.
`BernoulliHermitizationTheorem.lean` proves all three manuscript interface
conclusions and the exact negative circular-potential limit, including
singular samples in the failure event.
`BernoulliBottomLogTailTheorem.lean` proves the named bottom-tail corollary
and negative-log uniform integrability, retaining infinity at zero.
`BernoulliCircularLaw.lean` uses these results and the direct checked
hermitization criterion to prove full bounded-Lipschitz eigenvalue
convergence for the sparse Bernoulli law. These six modules add 20 theorems
and five definitions. Named coverage is now 23/29: the Bernoulli interface
and bottom-tail corollary are promoted to proved. The row-slice main theorem
and its remaining regime and smallest-singular-value obligations are open.
The rounded T2 auxiliary comparison remains under review and is not used
in these proofs. All manuscript hashes are unchanged.

The row-slice main theorem and both degree regimes are now proved in
`CircularLawProvedRegimes.lean`. Their source mapping is reviewed in
[CIRCULAR_LAW_STATEMENT_REVIEW.md](CIRCULAR_LAW_STATEMENT_REVIEW.md).
Named coverage is 26/29. The reviewed rounded auxiliary comparison is
not used in these proofs; its source formula is still unchanged. The
two quantitative joint minimum estimates and tensorization statement
review remain unfinished full-paper obligations.
