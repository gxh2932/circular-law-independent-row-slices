# Development history

This is the development log preserved at the October 10, 2026 publication
update. Progress counts, open obligations, and PDF-build limitations below
record earlier snapshots. For the completed status and current build
instructions, see [README.md](README.md). All 29 named results are now
proved, and the corrected manuscript PDF has been regenerated.

# Lean formalization of the independent row-slice circular law

**The full-paper Lean goal is complete: all 29 named manuscript results,
including the main circular-law theorem and both quantitative joint
smallest-singular-value estimates, have checked proofs.** The full build,
axiom audit and strict completion gate pass. All required mathematical
inputs are proved; no admitted proof or added mathematical axiom is used.

The main proof is `CircularLaw.main_circular_law_theorem` in
[CircularLawProvedRegimes.lean](CircularLaw/CircularLawProvedRegimes.lean).
The final joint estimates are in
[JointSmallestSingularTheorems.lean](CircularLaw/JointSmallestSingularTheorems.lean).
Their source mappings and validation are reviewed in
[CIRCULAR_LAW_STATEMENT_REVIEW.md](CIRCULAR_LAW_STATEMENT_REVIEW.md), and
[paper-coverage.json](paper-coverage.json) maps every named result.

Both minimum estimates use the actual row-slice and independent Bernoulli
laws. One fixed source-parameter choice supplies the rare and large
small-ball bounds, finite nets, all three steep classes, gradual classes,
square-adjoint and every omitted-row kernel event. The Bernoulli mean
correction includes its fluctuating row sums and their additional degree
term. The logarithmic-degree target holds at every admissible dimension,
with both exponents strictly above two and at most an absolute multiple
of log(log(n)). The superlogarithmic target has the same polynomial
exponent for both laws, one absolute probability coefficient independent
of epsilon, and a dimension threshold depending on epsilon.

The user approved the tensorization correction and both final manuscript
corrections on 2026-10-10. The latter makes the corollary's sufficiently
large dimension condition explicit and replaces the false rounded T2
comparison with the checked direct convergence of the actual minor
prefix T. The exact changes are retained in
[TENSORIZATION_CORRECTION.patch](TENSORIZATION_CORRECTION.patch) and
[FINAL_STATEMENT_CORRECTIONS.patch](FINAL_STATEMENT_CORRECTIONS.patch).
The existing PDF has not been regenerated because this environment has
no terminal TeX compiler; the corrected TeX and Lean targets are current.

Earlier development milestones follow; the coverage ledger and this
current status take precedence over their historical progress counts.

Every actual even Gaussian singular moment now converges in mean square
and probability at every complex shift. Compact moments construct the
unique singular weak limiting probability law, with bounded support,
linear mass near zero, no zero atom and finite logarithmic integral.
The actual empirical full logarithm and spectral logarithmic potential
also converge in probability to that integral at every shift, as do all
prefixes omitting a vanishing fraction. Extended bottom logarithmic
sums tend to zero for every `r=o(n)`. Equal-radius shifts have identical
limiting singular measures and logarithmic integrals.
The actual shifted word functional now satisfies the exact first-pair
recurrence, retaining every scalar shift and word order. At real shifts,
alternating words give coupled equations for the actual limiting moment
series and their cubic elimination. These are checked formal series
identities. Uniform geometric bounds identify the actual analytic squared
resolvent with this moment series near zero; the identity principle proves
its cubic on the entire left half-plane. The actual Hermitized resolvent
satisfies the scalar Dyson equation at every positive spectral parameter,
is positive and is bounded by one. Differentiation identifies the actual
regularized logarithmic integral with its explicit Dyson expression.
Removing regularization and computing both resolvent limits proves the
logarithmic value at every complex shift, equal to the actual circular
potential. Full Gaussian eigenvalue-measure convergence in bounded-Lipschitz
distance to the uniform unit disk is now proved with every input discharged.
Every limiting word mean is now identified with its exact compatible
noncrossing-pairing count. At zero shift, the actual limit is the
quarter-circle law with density `sqrt(4-s^2)/pi` on `(0,2)`. Its
logarithmic integral is `-1/2`, agreeing with the circular potential at
zero. Transfer of weak convergence to the actual sparse Bernoulli model
is proved below. Its full logarithmic limit is proved below; the row-slice regime
conclusions remain open.

The actual centered Bernoulli entry words now have exact product-moment
formulas, including all repeated indices and two-trace products. Sparse
normalization and scalar-shift expansion retain every finite walk. Removing
the constant mean matrix changes the actual empirical singular mass below
each threshold by at most `1/n`, at every sample. The visited-vertex graph
is connected, with at most one more vertex than distinct entries; equality
forces a tree. Exact colorings of each equality pattern have a falling
factorial count, whose dimension-normalized value tends to one. The actual
trace sum is now grouped by those finite patterns. Singleton entries vanish,
nonleading patterns lose a dimension or degree power, and each leading
paired pattern contributes one. Under `d->infinity` and `d/n->0`, every
actual centered normalized word mean has its leading-pattern-count limit;
odd word means tend to zero. Scalar-shift expansion gives every actual
centered shifted even singular-moment mean a finite nonnegative limit at
every complex shift. Exact two-walk covariance bounds prove mean-square
and probability convergence of all centered word traces and probability
convergence of every centered shifted even singular moment. A bijection
identifies the leading Bernoulli patterns with the Gaussian pairings.
High-moment tail bounds and polynomial approximation give the centered
weak law; clipped one-index interlacing restores the rank-one mean and
proves the actual uncentered Bernoulli weak law at every complex shift.
Both common comparator-prefix theorems now require only the degree
hypotheses. The same moment and covariance proofs now permit real
effective degrees and arbitrary growing minor dimensions. Restricting
the actual ambient sample gives the principal minor its unchanged entry
probability, and its weak law is checked after effective-degree normalization,
including the manuscript floor. The exact finite rescaling to the source
ambient normalization is checked. Relative-error weak transfer now proves
the actual minor weak law with that ambient normalization: its limit is
the sqrt(theta) pushforward of the Gaussian law at shift z/sqrt(theta).
The scaled law has checked small-value mass and support bounds, a finite
logarithmic integral and an exact circular-potential scaling correction
tending to the full value as theta tends to one. The literal retained prefix
has a fixed positive singular-value lower bound with probability tending
to one; its retained-zero probability vanishes. Actual minor second-moment
control and uniform logarithmic clipping now prove that the literal minor
`T` (`eq:SSS-T`) converges to the circular potential along one common positive antitone
slow fraction with the full-matrix `T1`. The source floors and ambient
denominator are retained. Every input to these two prefix limits is checked.
The actual Bernoulli full logarithmic limit follows conditionally from the
remaining fixed-fraction full-to-minor upper estimate with deterministic
and probability errors vanishing as the fraction shrinks. That estimate
remains unproved, so part (ii) stays open. The exposure-process
half-integer drift lemma is now checked, including its conditional
probability hypothesis, moving barrier and the zero-error case. The
coupling that kills height when a currently measurable graph condition
fails is also checked. The row-insertion singular-product inequality is now
checked with the actual projection onto the leading-row kernel, including
zero old products. Its dimension and near-kernel estimates, the interlacing
branch and the normalized logarithmic step are checked. Adjoint singular
values and finite reindexing now give the column step and literal last-row
and last-column deletion steps. The actual Bernoulli scalar small-ball
estimate is proved. A coordinate-spread orthonormal basis is now proved to
exist in every nonzero complex subspace: each vector has at least `h/4096`
coordinates of modulus at least `sqrt(h)/(64*n)`. Actual projection and
row/column log-step failure bounds therefore use positive subspace dimension
and compatible radii, with no assumed spread basis. The Bernoulli
large-dimension projection estimate is now proved at the source radius:
for `d=n*p>=1` and `h>=n*d^(-1/4)`, probability is at most
`C*(kappa+d^(-1/4))`. It permits ambient dimensions at most n, arbitrary
shifts and row conjugation. Actual row/column log-step failure bounds use
it with an explicit scalar threshold comparison. The small-dimension graph-spread projection regime and graph
probabilities are supplied below. Assembly of the alternating row/column
process remains open.

The deterministic graph coordinate-gap step is now checked for actual
shifted rectangular matrices. It includes both kinds of unique-neighbourhood
row, the embedded diagonal in the middle-coordinate support count, and
the exact fifth-power row threshold and seventh-power coordinate gap.
Under explicit unique-neighbourhood, heavy-row and column-degree budgets,
the image has at least half the expansion count of large coordinates.
Its squared-norm lower bound excludes this gap for a sufficiently small
matrix image. The actual source growth function now supplies the middle
budget from the uniform column-degree condition. Its integer recurrence
exits the source terminal scale in at most
`(4*C+2)*log(n/k)^4` steps, with an explicit fixed C. Coordinate propagation
through that recurrence and finite rank validity are checked. Applying
this to the proved initial spread basis gives an actual Bernoulli
projection bound, including `4*C_scalar/sqrt(log(log d))` at the source
terminal scale when `d=n*p`. The basis argument also covers initial
coordinate counts already beyond that terminal scale. The actual
leading-row kernel now supplies the uniform near-kernel estimate from its
next singular value, with scale zero when all rows have been retained.
A failed row or adjoint-column logarithmic step forces that scale below
`exp(-N*delta)`. Consequently the actual failure probabilities satisfy the
same graph projection bound under the graph events and explicit energy
and projection-radius comparisons for that threshold. Those scalar
comparisons are now discharged in the integer guarded exposure range,
using an explicit coefficient of the source eighth-power logarithms.
Both raw-matrix row/column branches are checked, with squared-log thresholds
in the large branch. The normalized projection bounds also retain the
`sqrt(d)` factor: doubling the small-branch coefficient absorbs that factor,
while the large branch has radius coefficient equal to the remaining
fraction. Their combined error is
`C_large*(epsilon+3*d^(-1/4))+4*C_scalar/sqrt(log(log d))`, tending to zero
as the fraction tends to zero and degree tends to infinity. These normalized
projection interfaces retain the actual next-singular-scale hypothesis.
Rectangular singular-value homogeneity now gives the degree correction
for actual inserted row and column matrices. Nonzero retained products
give the exact log-prefix correction. Positive raw growth by
`sqrt(d)*exp(-N*delta)` proves both a positive normalized new product and
the actual normalized log increment. Failure includes a zero new product.
The large next-singular-value branch makes failure impossible; the other
branch satisfies the combined normalized source probability bound under
the graph budgets. The literal accumulated rank-error sum is now bounded
by `32*sqrt(L/N)+C(K,beta)*log(d)^8*d^(-1/8)` and tends to zero as
`L/N->0` and `d->infinity`, with the integer small-branch cutoff retained.
Normalized projection, next-singular-value and same-rank steps now also
apply to the actual last-row and last-column matrix views, preserving
positive new retained products. A common slow-choice reduction permits
both deterministic and probability errors that vanish with the fraction.
The actual uniform column-degree event now fails with probability at most
`N^(-3)` at constant eight. For unit-bounded entries, this gives the actual
heavy-row budget when `d>=32`, including the source range `d>=exp(4)` and
`0<beta<=1`. Both budgets hold simultaneously for every injective row and
column restriction of the actual square Bernoulli matrix outside the same
failure event. The actual square law is invariant under adjoint, so both
orientations and all their restrictions satisfy these degree budgets
outside one event with probability at most `2*N^(-3)`. Exact row-pattern
probabilities and factorization also give the actual unique-neighbourhood
mean, exponential moment and lower tails for arbitrary fixed rectangular
column sets. Both diagonal-row and outside-row contributions are retained.
Small-set subset entropy is absorbed for both square and one-column
rectangular exposure laws at the original ambient degree `d=N*p`.
When `d>=exp(64)` and at least `3*N/4` rows remain, all sets with
`|S|>=k>0` and `|S|*p<=1/2` satisfy the source expansion except with
probability `2*exp(-d*k/16)` or `4*exp(-d*k/16)`, respectively. The larger
set range is also checked. For `d>=exp(1024)`, `p<=1/2`, at most N columns
and `0<beta<=1`, the full source expansion budget fails with probability
at most the small-set bound plus `N*exp(-N/(64*log(d)))`. Exact coordinate
marginals transfer these estimates to each specified ambient restriction,
including restrictions of the adjoint. Simultaneous graph bounds and
conditional insertion estimates are now checked, as described below.
Progressive graph events and the adapted rank process are now checked
below. Concrete conditional drift and the full-to-minor upper estimate
remain open. No claim of the full SSS25
Lemma 6.1 outside the guarded range is made.

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

`RegularizedRowSingularFormula.lean` identifies the actual ridge determinant
and potential with their singular-value product and logarithmic sum.
`RegularizedRowLogRemoval.lean` proves the finite removal bound
`k*eta^2/(2*tau^2)` and normalized error at most `1/(2*n^2)` for the exact
choice `eta=tau/n`. `RowRestrictionLogVolume.lean` transfers the square
smallest-singular-value lower bound to every actual retained row and
compares its log volume with both square singular-value sums.
`RowRestrictionDeterminantTails.lean` proves the manuscript determinant
comparison using precisely the top positive and bottom negative logarithms
of the deleted-row count. These four modules add 16 theorems and one
definition. The smallest-singular-value bound is an explicit hypothesis
in these supporting deductions; its required probabilistic proof and both
row-slice regime conclusions remain open. Named coverage remains 23/29.

`SingularPositiveLogEnergy.lean` proves the finite positive-log energy
estimate, including an empty prefix. `SingularBottomLogBounds.lean` splits
the bottom tail at the literal intermediate deletion count: those values
pay the assumed smallest-singular-value cost, and the remaining values
pay the actual intermediate scale. `RowReplacementProbability.lean`
supplies Markov bounds under the actual finite product of slice/Bernoulli
row pairs. `RowRestrictionVolumeProbability.lean` removes both ridge
errors with total normalized error `1/n^2` and keeps the joint minimum
failure event in the deviation probability. Its convergence transfer
still requires that event's vanishing probability and the regularized
comparison limit.

`HermitizationDeletionParameters.lean` retains `ceil(n/d^a)`, proves its
relative size tends to zero and supplies valid prefix dimensions
eventually. `HermitizationReplacementScale.lean` checks
`Q>=d^(1-a)/2`, supplies `Q>=1` eventually and verifies the manuscript's
balanced superlogarithmic exponent identities.
`HermitizationPositiveTailRates.lean` uses the actual shifted row-slice
energy to prove its positive-log tail vanishes uniformly over samples
for every fixed `0<a<=1`, covering both manuscript cutoffs. These seven
modules add 28 theorems and two definitions. Named coverage stays 23/29;
the probabilistic smallest-singular-value estimate and row-slice regime
conclusions remain open. No manuscript source
has changed.

`IndependentSquarePrefixLaw.lean` proves that the actual independent
row-slice and Bernoulli square samples supply the exact paired-row product
law for any injective row selection. `ShiftedSquarePrefixComparison.lean`
checks the original diagonal columns, maximum shift norm and both literal
hybrid endpoints, then transports expected and probability replacement
bounds to the actual square prefixes. `ShiftedReplacementUpperBound.lean`
proves the finite cap `U<=2*(1+abs(z))*sqrt(n)` and its logarithmic ratio
at `eta=tau/n`.

`HermitizationReplacementRates.lean` proves that its explicit error
envelope vanishes for every fixed `0<a<1` when the cutoff ratio has a
polynomial degree budget. `HermitizationCutoffBudgets.lean` discharges
that premise for both manuscript cutoffs from the logarithmic lower
degree bound. `HermitizationPrefixComparison.lean` proves the actual
normalized regularized prefix difference converges to zero in probability
at `a=1/2` and the exact balanced superlogarithmic exponent. Its latter
conclusion also accepts the source `(log(n))^(1+epsilon)<=d` hypothesis
directly. The volume convergence deduction now only needs finite measures,
covering all initial dimensions while retaining the joint minimum failure
probability as its remaining premise.

`IndependentSquareMinimumFailure.lean` supplies the exact square marginals,
equivalence with the last ordered singular value and joint failure union
bound. It transports proved individual failure limits, without claiming
the open imported estimates. These seven modules add 34 theorems, 11
definitions and one finite-measure instance. The probabilistic minimum
estimate and full regime conclusions remain open. The conditional bottom-tail
and raw determinant deductions are now checked below. Named coverage is
still 23/29, and all manuscript hashes are preserved.


`HermitizationBottomScalarRates.lean` and `RowSliceBottomLogBudgets.lean`
prove the literal bottom-log budgets at both deletion exponents. The
lower-band cost combines the intermediate `q0` minimum cost with the
remaining intermediate-singular-value scale; the superlogarithmic cost
tends to zero under the source power-degree hypothesis.
`RowSliceBottomLogProbability.lean` turns these bounds into actual coupled
row-slice bottom-tail convergence, retaining the joint minimum failure
limit as an explicit premise.

`SingularBottomScaling.lean`, `BernoulliHermitizationPositiveTail.lean` and
`IndependentBernoulliLogTails.lean` prove the actual raw Bernoulli positive
and negative logarithmic tail limits and transport them to the exact
independent coupling. `PrefixDeterminantErrorGeometry.lean` identifies
the bottom-index sum with the literal finite tail and bounds the actual
normalized determinant-volume error. `PrefixDeterminantErrorProbability.lean`
assembles that error with the four tails and actual prefix comparison.
`RowSliceRawLogDeterminantComparison.lean` then proves the raw determinant
comparison deduction in both source regimes. The lower-band deduction
uses the proved intermediate theorem directly. Both deductions still
require the actual joint minimum failure probability to tend to zero;
that imported input is not claimed as proved. These nine modules add 41
theorems and five definitions. Named coverage remains 23/29. The required
minimum estimates and recorded statement review remain unfinished. The
conditional normalized circular-law assembly is now checked below; all
manuscript sources are preserved.

`RowSliceNormalizedLogComparison.lean` proves the common determinant
normalization correction and its cancellation on the joint minimum event.
The proved Bernoulli logarithmic limit and exact marginal laws then supply
the actual normalized row-slice logarithmic limit, conditional on the
checked comparison. Agreement outside a vanishing bad event now requires
only finite measures.

`RowSliceCircularFromLogLimit.lean` proves deterministic degree-normalized
row-slice energy at most one per dimension, including zero degrees.
Clamping the degree to `min(d,n)` supplies probability spaces in all
initial dimensions and equals the original model eventually. The actual
logarithmic limit therefore gives both degree- and variance-normalized
circular convergence. `RowSliceConditionalCircularRegimes.lean` discharges
all these inputs in the lower-band and superlogarithmic deductions; the
lower-band constant is independent of sigma. Their only remaining
probabilistic inputs are the actual joint minimum failure limits.

`SmallestSingularFailureTransfer.lean` identifies the source's non-strict
minimum event, bounds the joint failure event by the two source events,
proves `C1/sqrt(d)->0`, transfers the bounded source exponents to the lower
cutoff and checks the fixed-shift restriction eventually.
`CompletedDegreeRegimes.lean` completes degree sequences outside each
regime, keeping their original values on that regime. The two-filter
assembly then proves the deduction of `MainTheorem` from the uniform
minimum failure limits. These five modules add 28 theorems and four
definitions. No imported probability estimate is asserted or added as
an axiom, and no named result is promoted. The actual smallest-singular-
value estimates and recorded statement review remain unfinished; named
coverage stays 23/29 and all manuscript hashes are preserved.

`InvertibilityDistanceGeometry.lean` and `InvertibilityDistanceProbability.lean`
prove LLY26a Lemma 7.1 for the actual finite laws. The non-almost-constant
unit-vector infimum has value infinity when its admissible set is empty;
the proof supplies a common strict distance gap before taking the infimum.
The probability bound uses the expected number of close rows and needs
no independence of the distance events.
`SmallestSingularDistanceReduction.lean` identifies the row combination
with the literal matrix adjoint action and constructs an actual unit
witness for every ordered singular value. The smallest-value failure is
therefore bounded by the source almost-constant failure probability plus
the average row-distance probabilities, including on the uniform shifted
row-slice law. These three modules add 17 theorems and five definitions.
The almost-constant and row-distance probability estimates themselves
remain unproved; named coverage stays 23/29 and all sources are unchanged.

`LeaveOneOutUnitNormal.lean` constructs a unit normal from the actual
other rows without a rank assumption. `ShiftedSliceUnitNormal.lean`
checks its invariance when the omitted row is resampled, the exact
shifted scalar form, and the inclusion of a bad normal in an actual
almost-constant kernel event for the other n-1 rows.
`LeaveOneOutDistanceProbability.lean` performs the finite-law conditioning
step of LLY26a Lemma 7.2 and assembles the smallest-value reduction from
the scalar concentration and two almost-constant probability estimates.
These component estimates are explicit premises of that deduction; the
scalar premise is discharged below.
`NonAlmostBernoulliSmallBall.lean` proves the Bernoulli scalar estimate
outright: its actual probability at radius `rho/sqrt(n)` is at most
`C/sqrt(delta*d)`, uniformly in the center, whenever `1 <= d <= n/2`.
These four modules add 26 theorems and three definitions. The fixed-degree
slice small-ball estimate is proved below. The square/leave-one-out
almost-constant probability estimates remain unproved. Named coverage
stays 23/29.

`UniformEmbeddingRestriction.lean` counts the exact fibres of restriction
to one sampled block. `PairedSliceSampling.lean` proves that selecting one
coordinate from each injectively sampled pair by independent fair Boolean
choices gives the actual uniform slice law, and checks its scalar form.
`FairBooleanSmallBall.lean` identifies those choices with the actual
Bernoulli half-parameter law. `PairedSliceSmallBall.lean` bounds slice
concentration by `C*(r/rho)/sqrt(k/2)` plus the actual probability of fewer
than k pairs separated by rho. These four modules add 17 theorems and
seven definitions. The pair-failure probability and full slice small-ball
estimate are now proved below. The almost-constant estimates remain open.
Named coverage stays 23/29 and manuscript sources are unchanged.

`UniformEmbeddingMarginal.lean` proves the uniform law of every injective
sampling restriction. `SeparatedPairMean.lean` gives the actual separated-pair
count mean at least `delta*d`. Finite fibre means, their tower identity,
exact prefix-swap couplings and Hoeffding's bound give a checked exponential
tail for uniform injection sampling. A transposition changes the actual
pair count by at most two, so `SeparatedPairLowerTail.lean` proves
`P(pair_count < delta*d/2) <= exp(-delta^2*d/64)`.

`RowSliceScalarSmallBall.lean` completes
[SSS23 Lemma 8.5](https://arxiv.org/html/2310.17635#S8): for `0<d`, `2*d<=n`,
positive delta and rho, and every radius-rho level set of size at most
`(1-delta)*n`, the actual slice concentration is at most
`2*C_B/sqrt(delta*d)+exp(-delta^2*d/64)`. The closed source theorem has
absolute constant `64+2*C_B`. `RowSliceNonAlmostMinimumBound.lean` turns this
into `C(delta)/sqrt(d)` and discharges the scalar premise in the actual
leave-one-out distance and minimum-value reductions. Only the square and
leave-one-out almost-constant probability bounds remain as premises there.
These 12 modules add 54 theorems and 13 definitions. Named coverage remains
23/29; the imported minimum estimates and main theorem remain unproved.

```lean
example : CircularLaw.SliceScalarSmallBallTheorem :=
  CircularLaw.slice_scalar_small_ball_theorem
```

The column-degree controls needed by the remaining almost-constant
argument are now checked. `RowSliceEdgeLowerTail.lean` proves the actual
multiplicative Chernoff bound `exp(-mu*theta^2/2)` using the already proved
negative-tilt exponential moment. `RowSliceColumnLowerBounds.lean` gives
failure at most `n*exp(-d/72)` for a square column below `5*d/6` and
`n*exp(-d/320)` for that same threshold after deleting one row, when
`n>=11`. It also converts both bounds to `n^(-A)` under explicit
logarithmic degree conditions.

`RowSliceColumnSubsetLoads.lean` proves the full deterministic
[LLY26a Lemma 5.2](https://arxiv.org/html/2604.10446v1#S5): every nonempty
row subset J has total column load `d*|J|`, hence at most `n/r` columns
with load at least `r*d*|J|/n`. The theorem also permits rectangular samples
and every positive r. `FiniteUniformEmbeddingRestriction.lean` proves
the exact finite product law under every injective coordinate restriction.
`RowSliceRetainedColumnLowerBounds.lean` transports the deleted-row
degree bounds to the actual square sample and every injective selection
of `n-1` rows. These five modules add 21 theorems and four definitions.
The steep-vector exclusion and full almost-constant probability estimates
in the minimum argument remain unfinished; named coverage stays 23/29.

The square adjoint's gradual almost-constant branch is now proved under
explicit rank, radius and shift budgets. `LLYSteepGeometry.lean` retains
the first jump chain, its terminal rank and the dense first-rank-one case,
then proves the coarser norm constant
`B=4*sqrt(n)*(if k1=1 then 1 else (6*d)^(r+1))*d^(3/4)`.
`LLYAlmostConstantBlocks.lean` constructs the four actual bad-coordinate
blocks and the constant center, with `delta*n<=k3` keeping the integer
count exact. `LLYColumnSurvivors.lean` uses deterministic total loads to
retain at least half the columns, separately keeping the second block's
cutoff `9*k2*d/n` and the later blocks' cutoff `9*k3*d/n`.

`SupportAlmostConstantAction.lean`, `LLYColumnBadMass.lean` and
`LLYColumnAction.lean` bound the actual bad mass, count the close entries
and identify the literal shifted adjoint coordinates with support sums.
`LLYGradualAdjoint.lean` proves that every unit gradual almost-constant
vector has adjoint image norm at least `2*d*sqrt(n)/(25*B)` when all
column degrees are at least `5*d/6`. For
`rho<=sqrt(n)/(5*B)` and every strictly smaller image threshold, its
failure probability is consequently at most `n*exp(-d/72)`. The required
rank budgets are `d*k1<=n/9`, `k2*d^(3/4)<=n/1000`, `k3<=n/1000`,
positive valid ranks, `k2<=k3`, `2*k3<=n` and `k1<=ell^(r+1)`;
the shift budget is `norm(zeta)<=4*d/25`.
`LLYAlmostAdjointReduction.lean` therefore bounds the full actual
almost-constant adjoint failure by the actual steep-adjoint failure plus
that proved exponential term. The steep probability and the complete
leave-one-out kernel bound remain unproved. These eight modules add
39 theorems and 14 definitions; named coverage remains 23/29. No sharper
imported norm constant is assumed, and no manuscript statement is changed.

The gradual branch for the actual retained right action is now checked
as well. `LLYRowLoadProbability.lean` takes the union over every small
coordinate subset at both ranks before a vector is selected. It proves
failure at most `exp(-(rowLoadRate/4)*n)` under explicit density, entropy
and dimension budgets, and discharges the degree-entropy and dimension
conditions eventually, uniformly for every `d>=C*log(n)` with fixed C>0.
`LLYRowSurvivors.lean` retains at least n/3 rows, and
`LLYRowAction.lean` controls the actual bad count and weighted modulus
using the separate cutoffs `16*k2*d/n` and `16*k3*d/n`.

`LLYGradualRetained.lean` gives every actual unit gradual almost-constant
vector the same lower image norm `2*d*sqrt(n)/(25*B)` on any retained
set of size at least `99*n/100`, then excludes it from that kernel.
`LLYLeaveOneOutReduction.lean` preserves the full-square sample and
ambient diagonal when one row is omitted. For n>=100, it bounds the
actual almost-constant kernel probability by the actual steep-kernel
probability plus `exp(-(rowLoadRate/4)*n)`.
`LLYGradualRadiusBudgets.lean` proves that the radius bound automatically
fits the threshold `rho^2/n`, and that `k1<=floor(n/(16*d))` supplies the
column top-block budget. `LLYSmallestReduction.lean` assembles the proved
scalar and both gradual branches: under the explicit budgets, its only
probability inputs are the actual steep-adjoint bound kappa and the
uniform actual steep leave-one-out bound eta. Its conclusion is
`kappa+n*exp(-d/72)+(C(delta)/sqrt(d)+eta+exp(-(rowLoadRate/4)*n))/delta`.
These seven modules add 24 theorems and three definitions. The steep
probability estimates, rank choices and exponent bounds still need proof;
named coverage remains 23/29 and the main theorem remains unproved.

The first steep right-kernel class is now proved on the actual row-slice
law. `LLYFirstSteepGeometry.lean` chooses the least six-degree jump in
the actual ordered coordinates and proves the norm constant
`B1=sqrt(n)*(6*d)^r`, retaining the clipped terminal rank.
`LLYFirstSteepAction.lean` uses every eligible unique-coordinate witness
to give each unit first-steep vector retained image norm at least
`sqrt(d)/(4*B1)` for `norm(zeta)<=d`. This simultaneously excludes those
vectors from every retained kernel on the witness event.

`LLYFirstWitnessProbability.lean` bounds actual uniform witness failure
by `(r+1)*exp(-(uniqueWitnessRate/2)*d)` under `16*d*k1<=n` and the
explicit stride entropy budget. `LLYFirstSteepProbability.lean` transfers
it to the actual small-image and one-row-deleted kernel events, retaining
the original diagonal index. The dense k1=1 first class is empty.
`LLYFirstWitnessBudgets.lean` derives the size budget from the existing
floor rank, discharges the entropy budget eventually for square-root
strides above an explicit logarithmic degree lower bound, and gives the
polynomial failure conversion with a checked scale-count bound.

`LLYMinimumFirstSteepReduction.lean` now leaves only the second/third
steep right-kernel probability and the full steep-adjoint probability
as probability inputs, charging the proved first-class term explicitly.
These six modules add 27 theorems and five definitions. The remaining
steep probabilities and full source parameter/exponent assembly remain
unproved; named coverage stays 23/29 and the main theorem remains unproved.

The first LLY steep adjoint class is now proved by
`RowSliceOutNeighbours.lean`, `RowSliceOutNeighbourLaplace.lean`,
`RowSliceOutNeighbourMean.lean`, `RowSliceOutExpansion.lean`,
`RowSliceColumnThreeHalves.lean`, `LLYUniqueColumnWitness.lean`,
`LLYColumnWitnessProbability.lean`, `LLYFirstSteepAdjoint.lean`
and `LLYLaterSteepReduction.lean`. The exact probability that a
coordinate set is avoided by independent fixed-size rows bounds
the negative Laplace transform of the actual occupied-column count.
This argument uses no column-independence assumption. Its exact mean
is `n*(1-(1-d/n)^s)`, and a fixed-set lower-tail bound is
`exp(-epsilon^2*d*s/8)` when `d*s<=epsilon*n`. Counting and entropy
absorption give a uniform expansion failure bound
`exp(-epsilon^2*d*s/16)` under the explicit entropy budget.

Expansion gives unique column witnesses for nested top-coordinate
sets, even after removal of the larger coordinate set to control
the diagonal shift. The actual `3*d/2` column-degree event controls
the adjoint tail. Every unit first-steep vector has actual adjoint
norm at least `sqrt(d)/(4*sqrt(n)*(6*d)^r)` on these events for
shifts of modulus at most d. First-class adjoint failure is at most
`(r+1)*exp(-epsilon^2*d/16)+n*exp(-2*sliceTailRate*d)` under the
explicit valid-rank, size, stride, entropy and image-threshold budgets.

The actual minimum-value reduction now requires only second/third
steep right-kernel and second/third steep-adjoint probability bounds;
both proved first-class error terms are charged explicitly. These
nine modules add 39 theorems and eight definitions. The later-class
bounds and complete source parameter/exponent assembly remain unproved. No named result is
promoted; coverage remains 23/29 and manuscript sources are unchanged.

The first-class image threshold is now discharged by
`LLYFirstRadiusBudgets.lean`. When the terminal rank differs from
one, the gradual norm constant dominates four times the first-steep
constant, and the existing gradual radius implies the strict
`rho^2/n` adjoint threshold. At rank one, the first class is empty
and its failure probability is zero.
`row_slice_smallest_probability_of_lly_second_third_bounds` no
longer takes an extra first-threshold comparison as an argument.

`BernoulliRowsSliceConditioning.lean` proves the exact event
identity for any selected row family. Each selected row pays
one support-size mass, yielding conditioning factor
`(4*exp(1)^2*sqrt(d))^m` for m rows.
`RowSliceSelectedAdjointSmallBall.lean` proves the transposed
Bernoulli product law and tensorizes the weighted scalar bound.
`RowSliceFullAdjointSmallBall.lean` fixes every other row, absorbing
its actual contribution into a deterministic center. The resulting
bound concerns the full shifted row-slice adjoint, with no
column-independence assumption on that row-slice matrix.

`OrderedAdjointSmallBall.lean` shows that an ordered gap supplies
m coefficients of modulus at least t after every constant shift.
At norm radius `sqrt(n)/3`, the proved fixed-vector bound is
`(4*exp(1)^2*sqrt(d))^m *
(4*exp(1)*bernoulliScalarSmallBallConstant/sqrt(m*d/n))^n`.
`SteepNetAdjointSmallBall.lean` applies it to every actual finite
steep-grid member and charges both exact net cardinalities in the
union bound. This estimate is useful in the later class where
`m*d/n` grows; the small-parameter second-class estimate still
requires a different bound. These six modules and the strengthened
reduction add 18 theorems and one definition. Later-class net
coverage, entropy absorption, right-kernel estimates and complete
source parameter/exponent assembly remain unproved. No named result
is promoted; coverage remains 23/29 and manuscript sources are unchanged.

`CenteredSliceAdjointError.lean` proves the actual centered adjoint action
and its zero-sum error bound. For coordinate error delta and scalar error
epsilon, the shifted-adjoint approximation error is at most
`(B+norm(zeta))*2*sqrt(n)*delta + (B+d+norm(zeta))*sqrt(n)*epsilon`,
where B bounds the actual centered complex operator. The expected matrix
therefore charges only the residual scalar error. `MeanCorrectedScalarNet.lean`
constructs and counts the finite fine grid covering the actual mean even
for sparse truncation errors.

`LLYThirdSteepNet.lean` covers the literal factor-four third class after
subtracting its almost-constant center. Its three grid ranges use the
actual LLY ranks, its tail is zero, and its ordered gap exceeds `2/3`.
`LLYThirdSteepAdjointProbability.lean` combines this cover with the proved
selected-row bound. `LLYThirdSteepNormalization.lean` proves homogeneity,
the third-class norm bound, and normalization of every actual almost-constant
unit-vector adjoint failure into that event. Its probability is bounded by
`n^(-A)` plus the exact vector/scalar net counts times
`(4*exp(1)^2*sqrt(d))^k2 *
(4*exp(1)*bernoulliScalarSmallBallConstant/sqrt(k2*d/n))^n`,
under explicit deterministic degree, radius and approximation budgets.

`LLYAlmostSteepSplit.lean` retains almost-constancy in the case split.
`source_almost_adjoint_probability_with_lly_third_net` in
`LLYAlmostAdjointThirdNet.lean` combines the checked first, third and
gradual bounds for the actual full almost-constant adjoint event; only
the second-class probability remains as an unestimated event term.
These seven modules add 32 theorems and ten definitions. The source-rank
budgets below discharge third-net entropy absorption. Second-class
estimates, later right-kernel bounds and full source parameter/exponent
assembly remain unfinished. No named result is promoted; coverage remains
23/29 and manuscript sources are unchanged.

`LLYThirdGridBudgets.lean` and `LLYThirdNetEntropy.lean` count the actual
three-range vector net and fine scalar grid. `LLYSourceRanks.lean` retains
the LLY26a Section 6 definitions: `epsilon0=sqrt(48*log(n)/d)`,
`ell=floor(1/(100*epsilon0))`, `n1=ceil(a1*epsilon0*n/d)`,
`n2=floor(a2*n/d^(3/4))`, and `n3=floor(a3*n)`.
`LLYSourceScale.lean` chooses `r=Nat.log ell (n1-1)` and proves the
required scale inequalities, including `n1=1`.
`LLYSourceRankValidity.lean` checks positive ranks, their required order,
and the half-dimension bound uniformly throughout the degree window.

`LLYThirdNetCardinalityUniform.lean` proves the literal vector/scalar net
product is at most `exp(n*log(d)/64)` eventually uniformly above
`C*log(n)`. `LLYThirdAdjointDecay.lean` absorbs both net counts and the
actual selected-row conditioning factor, giving `exp(-n*log(d)/32)`
uniformly for `C*log(n)<=d<=n/2` under the fixed constant restrictions.
`LLYThirdApproximationBudgets.lean` checks that the `d^(-3/4)` mesh fits
the actual centered-adjoint error budget throughout the spectral window
`norm(zeta)<=sqrt(d)*log(log(d))`.

`LLYThirdSourceProbability.lean` combines these estimates at the actual
rounded ranks and integer scale. `LLYSourceRadius.lean` constructs the
positive radius
`min(sqrt(n)/(5*Bgradual), d^(-3/4)*sqrt(n)/Bthird)` and proves the actual
unit-vector third almost-constant adjoint failure bound
`n^(-A)+exp(-n*log(d)/32)` at that radius. There are no separate rank,
entropy or mesh-budget hypotheses in this final third-class estimate.
These ten modules add 50 theorems and thirteen definitions. The
second-class and later right-kernel estimates, radius exponent and full
source assembly remain unproved. Named coverage remains 23/29 and all
manuscript source hashes are preserved.

`RareBernoulliAtoms.lean` proves the exact zero and single-selection
masses for arbitrary finite Bernoulli cubes. `RareBernoulliSmallBall.lean`
uses them to bound every scalar ball of radius `t/3` by `1-m*p/2` when
`m*p<=1/2` and all selected coefficients have modulus at least t.
`RareSmallBallTensorization.lean` gives `exp(-m*p*n/8)` at squared norm
threshold `t^2*m*p*n/72`, retaining the rare coefficient density.

`RareRowSliceSelectedAdjoint.lean` transfers this estimate to exact
fixed-degree selected rows and absorbs their actual conditioning cost.
`RareRowSliceFullAdjoint.lean` fixes all unselected rows as the center,
giving the original full shifted-slice adjoint probability bound
`exp(-m*d/16)` at squared threshold `t^2*m*d/72`. Ordered gaps provide
the m large coefficients after every constant shift.
`RareSteepNetAdjoint.lean` gives the norm threshold `sqrt(m*d)/30` and
the exact vector/scalar finite-net union bound.
`RareLLYSourceFirstCoefficients.lean` applies the fixed-vector estimate
at the literal source first/second ranks, uniformly throughout
`C*log(n)<=d<=n/2`, including the first-rank-one case.

`LLYFirstScaleEntropy.lean` bounds the total first-jump weighted grid
cost by `10*n1`; at `n1=1` it is zero. `LLYFirstScaleCoordinateBounds.lean`
checks the remaining coordinate cap from each actual first-jump scale,
including the normalized second steep class. These nine modules add
32 theorems and four definitions. They supply the coordinate caps and scale sums used by the refined
second-class net below. Its source-budget absorption remains required.
Later right-kernel estimates, the radius exponent and complete source
assembly also remain unproved. Named coverage stays 23/29 and all
manuscript source hashes are unchanged.

The actual second steep-class net is now constructed in
`LayeredSparseGridNet.lean` and `LLYSecondSteepNet.lean`. Disjoint
ordered-prefix increments telescope to the truncated vector, retaining
an individual coordinate cap and sparse grid at every first-jump scale.
The filtered net preserves the actual first/second ordered gap.
`SmallSetPowerBound.lean` counts all supports of size at most s by
`(n+1)^s`, including the empty-support case.

`LLYSecondNetEntropy.lean` counts the literal vector/scalar product.
Its log cost is at most
`5*n1*log(n+1)+(40*n1+3*(n2-1)+5)*log(d)+n*smallSetEntropy(a)`
under the stated second-prefix density condition. The weighted scale
cost is at most `10*n1`, the support sum at most `5*n1`, and both
first-prefix costs vanish for `n1=1`.
`LLYSecondSteepAdjointProbability.lean` connects actual normalized
second-class failure to the finite net, with mean correction charged
to the centered operator norm. `LLYSecondSteepNormalization.lean`
checks the unit-vector reduction. The resulting actual whole-class
probability is at most `n^(-A)+exp(-n1*d/32)` under explicit rare-density,
conditioning, approximation and entropy budgets.

These six modules add 31 checked theorems and twelve definitions.
Discharging the second-class budgets uniformly at the literal source
parameters, later right-kernel estimates, the radius exponent and full
source assembly remain unfinished. Named coverage stays 23/29, and
all manuscript source hashes remain unchanged.

The second-class source budgets are now discharged in
`LLYSecondSourceEntropy.lean`, `LogLogPowerBudgets.lean`,
`LLYSecondApproximationBudgets.lean` and `LLYSecondSourceProbability.lean`.
The literal first/second ranks and source integer scale give an actual
vector/scalar net product at most `exp(n1*d/32)`, uniformly for
`C*log(n)<=d<=n/2`. The spectral-window mesh error fits
`sqrt(n1*d)/60`, and the existing third-class radius supplies the second
unit-vector residual allowance. The second class is empty when its rank
order is reversed; no additional source rank-order premise is assumed.

`LLYSecondAdjointDecay.lean` proves that the actual first-rank exponential
is below every polynomial rate uniformly for `d<=n`.
`LLYSecondSourcePolynomial.lean` proves actual second-class unit adjoint
failure probability at most `n^(-A)` at threshold `rho_source^2/n`.
This holds eventually uniformly for `C*log(n)<=d<=n/2`,
`norm(zeta)<=sqrt(d)*log(log(d))`, `C>=1920000`, `0<a1<=1`, `a2>0`,
`A>=0` and `A+4<=9*C`. The almost-constant subevent has the same bound.
No independent entropy, conditioning, rare-density, rank-fit or mesh
budget remains in this probability estimate.

These six modules add 25 checked theorems and one definition.
Later right-kernel estimates, remaining first/gradual source parameter
budgets, the radius exponent and full minimum/regime assembly remain
unfinished. Named coverage stays 23/29, and all manuscript source hashes
remain unchanged.

The second steep right-kernel branch is now proved in
`RareRowSliceSmallBall.lean`, `RareRowSliceRightAction.lean`,
`MeanCorrectedRetainedNet.lean`, `LLYSecondSteepKernelProbability.lean`
and `LLYSecondSourceKernelProbability.lean`.
Singleton exposure of two equal separated blocks gives exact-slice
small-ball probability at most `1-m*d/(2*n)`. The rare-density condition
is `m*d/n<=1/4` or `m=1`; the rank-one case includes `d=n/2`.
Independent retained rows give `exp(-m*d/16)` at image norm threshold
`sqrt(m*d)/30` on every deterministic set of at least `n/2` rows.

The centered right-action error uses the same mean-corrected scalar net
as the adjoint estimate. Normalizing the first ordered rank covers all
second-class kernel vectors. At the literal source ranks and scale,
all rank-fit, rare-density, entropy, mesh and centered norm budgets are
discharged, including empty classes with reversed rank order.
For `C>=1920000`, `0<a1<=1`, `a2>0`, `A>=0` and `A+4<=9*C`, actual
second-class retained kernel failure probability is at most `n^(-A)`,
eventually uniformly for `C*log(n)<=d<=n/2` and
`norm(zeta)<=sqrt(d)*log(log(d))`. This includes every leave-one-out set.

These five modules add 21 checked theorems and two definitions.
The third-class right-kernel estimate, remaining first/gradual source
budgets, radius exponent and full minimum/regime assembly remain
unfinished. Named coverage stays 23/29; all manuscript sources are
unchanged and the main theorem remains unproved.

The almost-constant third steep right-kernel branch is now proved at the
literal source ranks, scale and source radius. Direct exact-slice
occupancy tails control the number of separated pairs even when the
high block has vanishing density. Scalar small balls tensorize over
independent retained rows without an additional conditioning cost.
The actual vector/scalar net cost leaves `exp(-n*log(d)/64)`.

For `C>=1920000`, `0<a1<=1`, `a2>0`, `0<a3<=1/4096`,
`12288*a1<=C*log(2)`, `alpha<=a3/2`, `A>=0` and `A+4<=9*C`,
the unit almost-constant third-class kernel probability is at most
`n^(-A)`, eventually uniformly for `C*log(n)<=d<=n/2` and
`norm(zeta)<=sqrt(d)*log(log(d))`. This holds for every deterministic
retained set with at least `n/2` rows and every leave-one-out set.
The almost-constant condition is required by the cover and remains
in the event. Its source rank, grid, entropy and norm budgets are
fully discharged.

These ten modules add 40 checked theorems and 7 definitions.
Preserving that condition in the full minimum reduction, remaining
first/gradual source budgets, the radius exponent and final
minimum/regime assembly remain unfinished. Named coverage stays
23 of 29; the main theorem remains unproved.

The full row-slice minimum estimate now combines all three steep classes
and both gradual branches at the explicit source radius `rho`. Under the
fixed degree, rank, density and entropy restrictions in
`eventually_lly_source_row_slice_minimum_probability`, the actual square
matrix has smallest-singular-value failure probability at most
`(5+(sliceSmallBallDegreeConstant(alpha)+4)/alpha)/sqrt(d)` at threshold
`rho^2/n`, eventually uniformly for `C*log(n)<=d<=n/2` and
`norm(zeta)<=sqrt(d)*log(log(d))`.

The third kernel branch preserves almost-constancy. Charging the strict
first prefix `k1-1` handles the dense rank-one case; the previous coarser
interfaces remain proved. Four new modules and six strengthened existing
modules add 28 checked theorems. The manuscript radius exponent, required
Bernoulli counterpart and final regime assembly remain unfinished.
Named coverage stays 23 of 29; the main theorem remains unproved.

The actual row-slice minimum estimate now supplies both manuscript
scales: `n^(-CL*log(log(n)))` under the logarithmic degree cutoff and
one fixed `n^(-B_epsilon)` throughout every superlogarithmic cutoff.
The literal rounded stride gives
`log(d)<=log(1920000)+log(log(n))+2*log(ell)`, including the dense
first-rank-one case. A proved choice of absolute constants discharges
all numerical, entropy and density requirements.

The resulting failure probability is at most a fixed constant divided
by `sqrt(d)` at both cutoffs. Its actual row-slice-law probability tends
to zero along arbitrary sparse degree sequences, for every fixed complex
shift. Four modules add 24 checked theorems, three definitions and one
parameter structure. The radius-exponent conversion and the row-slice
minimum inputs for both regimes are now proved. The Bernoulli minimum
counterpart, joint estimates and final regime/main assembly remain
unfinished. Named coverage stays 23 of 29; the main theorem is unproved.

The actual Bernoulli normalized singular-array logarithmic tails now remove
regularization on every retained row set for any positive ridge tending
to zero. A checked finite tail bound charges small reference values to
their negative logarithmic tail and bounds the remaining error by the
squared ridge scale. The extended full-log theorem also proves that the
actual raw Bernoulli determinant-zero probability tends to zero. Both
results transport to the paper's independent square coupling.

The proved row-slice minimum probability and the Bernoulli tail argument
now supply the unregularized prefix volume comparison from the checked
regularized comparison. Four modules add 13 checked theorems and one
definition. The required determinant tails, normalization and final
regime/main assembly still need to be connected to this interface; the
quantitative Bernoulli minimum counterpart and joint imported estimates
remain unfinished. Named coverage stays 23 of 29; the main theorem is
unproved.

The exact integer-rounded upper comparison `eq:SSS-T-upper` also needs
revision: a checked Bernoulli sample gives one extra logarithmic term in
the current `T2`. See [the hermitization statement review](HERMITIZATION_REVIEW.md).

The project uses Lean 4.28.0 and mathlib v4.28.0. `lake-manifest.json` pins
mathlib and its dependencies to exact commits. The manuscript remains the
source of the mathematical claims; this directory records which arguments
have been checked by Lean.

## Build and audit

Install [Lean through elan](https://lean-lang.org/install/), then run from
this directory:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Audit.lean
python3 scripts/paper_coverage.py
python3 scripts/test_paper_coverage.py
python3 scripts/test_axiom_audit.py
```

The full-paper completion check is separate:

```sh
python3 scripts/paper_coverage.py --require-complete
```

**That command passes with 29/29 proved and no open, partial or
statement-only results.** The GitHub workflow includes the strict check,
full build and axiom audit. A module build alone does not satisfy the
full-paper requirement.

The repository includes a GitHub Actions workflow using the official
[Lean action](https://github.com/leanprover/lean-action). The workflow builds
the project and checks all public project declarations for axiom dependencies.
It permits only `propext`, `Classical.choice`, and `Quot.sound`, the standard
foundations used by Lean/mathlib. Admitted proofs and additional axioms fail
the audit. The audit shares its visited-dependency state across declarations,
so common proof dependencies are traversed once while all project declarations
remain covered. The rejection test temporarily denies `Classical.choice` and
checks that the audit rejects that existing transitive dependency; it adds
no axiom or admitted proof. The audit checks the complete project and
explicitly type-checks the unconditional main target. The coverage checker resolves each claimed declaration and
type-checks every completed proof against its named target proposition.
Repeated declaration names are checked once, and Lean uses a larger thread
stack for the growing ledger. Integrity tests also require the valid
catalog to pass and a nonexistent supporting declaration to fail.
It records hashes of all manuscript TeX sources, including definitions
and macros, so source changes require a review of the mapping. Matching
the English/TeX statement to its Lean target remains a mathematical review
obligation; a source hash cannot establish that equivalence by itself.

## Checked results

| File | Checked content | Manuscript location |
| --- | --- | --- |
| [RowSlice.lean](CircularLaw/RowSlice.lean) | Exact-support model; cardinalities of row and matrix sample spaces; nonempty slices; zero-one entries; fixed row sum; all-ones eigenvector relation; centering; exact squared Hilbert--Schmidt norm; positive bulk scale | Section 1; centering in Section 6 |
| [FiniteProbability.lean](CircularLaw/FiniteProbability.lean) | Finite uniform event probabilities lie in `[0,1]`; full event has probability one on a nonempty space; rectangular events factor into coordinate probabilities; independent uniform row law | Section 1 model |
| [Marginal.lean](CircularLaw/Marginal.lean) | Counts supports containing a fixed coordinate and proves its marginal probability is `d/n`, using deletion rather than coordinate independence | Section 1 model |
| [Moments.lean](CircularLaw/Moments.lean) | Entry expectation `p`, variance `p*(1-p)`, and exact identity between `bulkScaleSq` and `n` times that variance | Section 1 normalization |
| [MeasureModel.lean](CircularLaw/MeasureModel.lean) | Counting probabilities equal a finite uniform measure; finite expectations equal its integrals; the matrix law equals the product of row laws; row marginals and independence are proved; tensorization applies to the same counting model | Section 1 model; tensorization in Section 2 |
| [Covariance.lean](CircularLaw/Covariance.lean) | Exact subset and pair inclusion probabilities, negative covariance within a row, real and complex linear-form second moments, and the exact isotropic scale on zero-sum vectors | Row-slice model and normalization |
| [Conditioning.lean](CircularLaw/Conditioning.lean) | Every slice has exactly `d!` ordered injective realizations; the conditioned support law is uniform; proves the exact transfer factor `(n^d/(n)_d)^K` for arbitrary matrix events and the bound `exp(2*K*d^2/n)` | Section 3, conditioning to slices |
| [FiniteConditioning.lean](CircularLaw/FiniteConditioning.lean) | Law of total expectation and probability over finite statistic fibers, including empty fibers; averaging fiber-constant bounds; independent convolution cannot increase concentration | Section 3, conditioning and averaging |
| [ProfileConditioning.lean](CircularLaw/ProfileConditioning.lean) | Count fibers are equivalent to label assignments times independent uniform block samples; exact conditional sum law; conditional and averaged estimator assembly with geometric block bounds explicit; the sampled sum equals the actual matrix row action | Section 3, `eq:conditional-block-sum` and supporting arguments for `lem:conditional-row-small-ball` |
| [PlanarPacking.lean](CircularLaw/PlanarPacking.lean) | Balanced-level maximum atom `4/(h+3)`; sharp planar packing bound `(1+2*r/delta)^2`; spread-part concentration bounds; verifies the Esseen and Miroshnikov single-summand hypotheses for degree at least `65536` | Section 3, atom and packing inputs to the conditional row lemma |
| [CharacteristicDefect.lean](CircularLaw/CharacteristicDefect.lean) | Symmetrization of an arbitrary probability law and the integer-frequency estimate `1 - abs(phi(k*t))^2 <= k^2*(1-abs(phi(t))^2)` | Fourier input to the planar concentration imports |
| [FourierLevels.lean](CircularLaw/FourierLevels.lean) | Area of near-one Fourier superlevel sets is at most `64*delta^2/3`; the normalized energy bound gives a `200/q` power-integral estimate for real `q>=2` | LLTTY19 Lemma 2.6 argument, with a looser absolute constant |
| [FourierPlancherel.lean](CircularLaw/FourierPlancherel.lean) | The classical Fourier integral equals mathlib's L2 transform almost everywhere for every L1/L2 input; proves pointwise Plancherel without a smoothness assumption | Discharges the energy identity used in the Fourier-power argument |
| [BoundedDensity.lean](CircularLaw/BoundedDensity.lean) | Actual planar probability density bounded by one almost everywhere yields the energy bound and the closed `200/q` Fourier-power lemma | Fourier-power dependency of LLTTY19 Proposition 2.4; no energy estimate remains assumed |
| [FourierProduct.lean](CircularLaw/FourierProduct.lean) | For `m>=2` bounded probability densities, the product of their Fourier moduli is integrable and its integral is at most `200/m`, by arithmetic-geometric mean | Integral estimate for the density of an independent sum |
| [FourierInversion.lean](CircularLaw/FourierInversion.lean) | Almost-everywhere classical Fourier inversion for L1/L2 functions whose transform is integrable; bounds a probability density by the integral of its Fourier modulus | Inversion step in LLTTY19 Proposition 2.4 |
| [DensityMeasure.lean](CircularLaw/DensityMeasure.lean) | Radon--Nikodym density of an area-dominated probability law, exact reconstruction of its law, domination under convolution, and closed-disk probability from a density bound | Actual density representation and concentration bridge |
| [SumLaw.lean](CircularLaw/SumLaw.lean) | Characteristic function of the actual product-law sum; convolution recursion; area domination of the sum | Independent-sum law in LLTTY19 Proposition 2.4 |
| [PlanarSumDensity.lean](CircularLaw/PlanarSumDensity.lean) | Closed planar sum-density theorem with constant `200/m` for every `m>=1`; transfer to independent random variables on arbitrary probability spaces; small-ball and concentration corollaries | LLTTY19 Proposition 2.4, identifying the complex plane with R2 |
| [PlanarDensityScale.lean](CircularLaw/PlanarDensityScale.lean) | Real dilations and their planar area factors; arbitrary density bound `B` gives sum density bound `200*B/m` and disk probabilities | Scaling step for discrete smoothing |
| [PlanarDisk.lean](CircularLaw/PlanarDisk.lean) | Uniform disk law has mass one, bounded support, reflection symmetry, zero mean, and second moment at most the squared radius | Actual smoothing noise |
| [IndependentSecondMoment.lean](CircularLaw/IndependentSecondMoment.lean) | Independent centered complex sums have additive second moments; a sum of `m` uniform disk samples of radius `r` lies within radius `2*sqrt(m)*r` with probability at least `3/4` | Discharges the noise probability estimate in smoothing |
| [DiskSmoothing.lean](CircularLaw/DiskSmoothing.lean) | Convolution with uniform disk noise turns a radius-`r` small-ball bound `u` into area domination by `u/(pi*r^2)` | Density of each smoothed discrete summand |
| [ConvolutionConcentration.lean](CircularLaw/ConvolutionConcentration.lean) | Small-ball rectangles give a lower bound for convolution; summandwise convolution equals convolution of the actual sum laws; combines noise probability and density bounds | Transfer from smoothed sum to original sum |
| [SeparatedLaw.lean](CircularLaw/SeparatedLaw.lean) | A closed disk with diameter smaller than the support separation contains at most one atom; maximum atom bounds its probability without a finite-support assumption | Separated-support hypothesis in LLTTY19 Proposition 2.5 |
| [DiscreteConcentration.lean](CircularLaw/DiscreteConcentration.lean) | Closed discrete planar sum-concentration theorem `10000*max(u*t^2/(m*delta^2),u)`; holds for independent summands with common separation and atom bounds, on any probability space | LLTTY19 Proposition 2.5, including its iid case |
| [RegularBlock.lean](CircularLaw/RegularBlock.lean) | Transfers separated balanced levels to the actual finite uniform sample law; checks independence and marginal laws; proves the regular block bound `40000*tau^2/(h*m/d)` at radius `tau*sqrt(d)/k` | Regular-part branch of the conditional row-local lemma |
| [Discretization.lean](CircularLaw/Discretization.lean) | Literal canonical floor approximation; equivalence with the scaled integer lattice; error at most `sqrt(2)/k`; distinct lattice values are `1/k` separated | Section 2, `def:k-vector` |
| [LevelSlices.lean](CircularLaw/LevelSlices.lean) | Actual leftmost-level selection, size bounds, factor-four balance, disjoint orders, and eventual exhaustion | LLTTY19 Section 5.2 |
| [LevelPartition.lean](CircularLaw/LevelPartition.lean) | Selected levels of the actual vector cover all coordinates; unions of represented levels have the size-height bounds | Section 2, `eq:part-size-height` |
| [CanonicalRemainder.lean](CircularLaw/CanonicalRemainder.lean) | The per-level recursion equals the global remaining-coordinate procedure; represented values equal the remainder's image; the successor deletes all current selected levels | Source correspondence for the construction |
| [GreedySpread.lean](CircularLaw/GreedySpread.lean) | Source lexicographic seed and decreasing greedy scan; separation, covering, two-value minimum, and the no-separated-pair case | LLTTY19 Section 5.2 |
| [CanonicalParts.lean](CircularLaw/CanonicalParts.lean) | Actual spread and regular parts, size-height bounds, regular-value geometry, explicit level fibers, balanced counts, and the regular-part block bound | Sections 2–3, canonical parts and regular concentration |
| [LevelInvariants.lean](CircularLaw/LevelInvariants.lean) | Nested represented value sets; heights and sizes invariant under coordinate permutation; logarithmic bound on nonempty orders | LLTTY19 Lemmas 5.3–5.4 invariants |
| [CanonicalPartition.lean](CircularLaw/CanonicalPartition.lean) | Actual nonempty parts form a disjoint cover; constructs their surjective coordinate map and `RowProfile`; verifies exact fibers and size-height bounds | Section 2 canonical profile |
| [CanonicalProfile.lean](CircularLaw/CanonicalProfile.lean) | Source enumeration: spread parts first, then regular parts, each in increasing order; eventual part count at most `3*log(n)`; heights at most dimension | Sections 2–3 profile hypotheses |
| [CanonicalRow.lean](CircularLaw/CanonicalRow.lean) | Regular inverse-weight bound for the actual count-conditioned row; averaged estimator for the ordered canonical profile with the height hypothesis proved | Supporting proofs for the conditional and averaged row results |
| [CanonicalSpread.lean](CircularLaw/CanonicalSpread.lean) | Actual spread-part atom bound and both single-summand concentration hypotheses from the constructed geometry and level sizes | Inputs to the spread-sum concentration estimates |
| [PlanarGaussian.lean](CircularLaw/PlanarGaussian.lean) | Planar Gaussian integral and Gaussian Fourier identity, including kernel integrability | Analytic input to LLTTY19 Proposition 2.2 |
| [GaussianConcentration.lean](CircularLaw/GaussianConcentration.lean) | Fubini for an actual probability law and the Gaussian characteristic-function small-ball bound | General planar concentration |
| [GaussianSumConcentration.lean](CircularLaw/GaussianSumConcentration.lean) | Independent characteristic-function product bounded by the exponential of symmetrized defects; actual independent-sum law | General planar concentration |
| [TruncatedSymmetrization.lean](CircularLaw/TruncatedSymmetrization.lean) | Concentration deficits bounded by truncated difference second moments for arbitrary laws | LLTTY19 Proposition 2.2 |
| [GaussianLattice.lean](CircularLaw/GaussianLattice.lean) | Gaussian integer samples controlled by their integral; summability of both tails | Periodic cosine integral |
| [PeriodicCosine.lean](CircularLaw/PeriodicCosine.lean) | Quadratic cosine-defect bound on one period and the Gaussian integral estimate across all periods | Analytic concentration input |
| [PlanarCosine.lean](CircularLaw/PlanarCosine.lean) | Rotation and rescaling extend the periodic bound to every nonzero planar direction | Analytic concentration input |
| [TruncatedCosineBound.lean](CircularLaw/TruncatedCosineBound.lean) | Uniform normalized single-vector integral bound `96/(r*sqrt(A))` | Truncated moment concentration estimate |
| [WeightedJensen.lean](CircularLaw/WeightedJensen.lean) | Actual moment-tilted probability law and weighted exponential Jensen, including zero weights | Truncated moment concentration estimate |
| [TruncatedGaussianMixture.lean](CircularLaw/TruncatedGaussianMixture.lean) | Weighted Jensen and checked product integrability give the Gaussian mixture bound by Fubini | Truncated moment concentration estimate |
| [EsseenConcentration.lean](CircularLaw/EsseenConcentration.lean) | Full planar Esseen estimate for arbitrary independent laws with constant `24*exp(1)/pi`; zero-deficit case included | LLTTY19 Proposition 2.2 |
| [CubeConcentration.lean](CircularLaw/CubeConcentration.lean) | Actual square concentration and the exact disk/square comparison at radius `sqrt(2)*r` | Geometry of LLTTY19 Proposition 2.3 |
| [CubeMedian.lean](CircularLaw/CubeMedian.lean) | Exhaustion by integer-scale cubes and the first scale at which any summand has more than half its mass in a translated cube | Miroshnikov median selection |
| [CubeConvolution.lean](CircularLaw/CubeConvolution.lean) | Localized convolution integrals and the half-mass removal recurrence for actual laws | Miroshnikov recurrence |
| [CubeSum.lean](CircularLaw/CubeSum.lean) | Removal of any summand from the actual product-sum law and the enlarged-cube Esseen bound | Independent-sum recurrence |
| [MiroshnikovStep.lean](CircularLaw/MiroshnikovStep.lean) | First-scale selection and Esseen prove the one-summand removal inequality | Miroshnikov proof |
| [CubeMiroshnikov.lean](CircularLaw/CubeMiroshnikov.lean) | Strong induction closes the removal recurrence for arbitrary finite nonempty families | Miroshnikov proof |
| [MiroshnikovConcentration.lean](CircularLaw/MiroshnikovConcentration.lean) | Full arbitrary independent planar estimate with the exact maximum single-summand radius `sqrt(2)*r` | LLTTY19 Proposition 2.3 |
| [UniformSumConcentration.lean](CircularLaw/UniformSumConcentration.lean) | Product-sum laws equal actual uniform sample sums; counting-probability interfaces and the five-sixths Esseen estimate | Spread-block sample law |
| [SpreadBlock.lean](CircularLaw/SpreadBlock.lean) | Both height branches give `C*tau^2/(h*sqrt(m))`; includes the trivial large-radius case | Spread branch of the conditional row lemma |
| [CanonicalSpreadSum.lean](CircularLaw/CanonicalSpreadSum.lean) | Applies the spread-sum bound to the constructed parts and their exact profile fibers | Section 3 canonical spread blocks |
| [ConditionalRow.lean](CircularLaw/ConditionalRow.lean) | Full conditional row-local lemma for every feasible profile; no block bound remains an argument | `lem:conditional-row-small-ball` |
| [AveragedRow.lean](CircularLaw/AveragedRow.lean) | Both averaged-profile conclusions with a common absolute constant, finite coordinate-mass law, and every deterministic scalar shift | `prop:averaged-profile` |
| [UniformRowsTensorization.lean](CircularLaw/UniformRowsTensorization.lean) | Tensorization for the exact finite independent row-sampling law | Section 3 matrix estimate |
| [ProfileTensorization.lean](CircularLaw/ProfileTensorization.lean) | Actual matrix action, Euclidean norm, deterministic vector shifts, profile tensorization, and exponential conditioning cost for row slices | Section 3, `eq:profile-tensorization-general` and slice conditioning |
| [EqualBlockAtom.lean](CircularLaw/EqualBlockAtom.lean) | Equal disjoint halves have mass one half; coefficient separation prevents a small disk from meeting both halves | Section 4 equal-block single-summand bound |
| [SingletonBlockCompletion.lean](CircularLaw/SingletonBlockCompletion.lean), [SingletonBlockFiber.lean](CircularLaw/SingletonBlockFiber.lean) | Exact support completion with one coordinate per active block; cardinality, sums and the equivalence from an actual fixed-degree row fiber to independent block choices | Section 4 row exposure |
| [DependentUniformSum.lean](CircularLaw/DependentUniformSum.lean), [SingletonBlockConcentration.lean](CircularLaw/SingletonBlockConcentration.lean) | Actual finite product-sum law and its one-half and Esseen concentration estimates, transported to the row-support fiber | Section 4, `eq:block-Esseen` |
| [SingletonExposure.lean](CircularLaw/SingletonExposure.lean), [SingletonExposureConcentration.lean](CircularLaw/SingletonExposureConcentration.lean) | Singleton mask and all fixed non-singleton positions determine the actual exposure fiber; concentration and deterministic constant-vector/diagonal centers | Section 4, conditioning and center invariance |
| [FiniteProductFibers.lean](CircularLaw/FiniteProductFibers.lean), [ProductFiberNorm.lean](CircularLaw/ProductFiberNorm.lean) | The joint coordinatewise exposure fiber is the product of uniform row fibers; unused rows integrate out exactly | Section 4 conditional independence across rows |
| [IndependentWitnessTail.lean](CircularLaw/IndependentWitnessTail.lean), [WitnessNorm.lean](CircularLaw/WitnessNorm.lean), [IndependentLogTail.lean](CircularLaw/IndependentLogTail.lean) | Actual event-count Laplace transforms; small squared norm forces at least seven eighths of the small-ball events; exponential and logarithmic independent-event bounds | Section 4 binomial norm estimate |
| [WitnessSelection.lean](CircularLaw/WitnessSelection.lean) | Double counting singleton witnesses; `B*q` total witnesses leave at least `3*B/4` rows above `B*q/(4*n)` | Section 4, `eq:sum-bi` and selected rows |
| [EqualBlockFiberNorm.lean](CircularLaw/EqualBlockFiberNorm.lean), [ExposedEventIntegration.lean](CircularLaw/ExposedEventIntegration.lean), [EqualBlockSelectedNorm.lean](CircularLaw/EqualBlockSelectedNorm.lean) | Both norm bounds for literal shifted row actions on the actual exposure fibers; the witness-size event stays inside the probability when the estimate is integrated | Section 4 fixed-vector mechanism |
| [EqualBlockEuclidean.lean](CircularLaw/EqualBlockEuclidean.lean), [EqualBlockWitnessNorm.lean](CircularLaw/EqualBlockWitnessNorm.lean) | Euclidean norm estimates on one-block and per-block witness events, for separated equal halves and uniform row slices; includes the logarithmic large-witness bound | Witness estimates in `lem:equal-block` |
| [OrderedCoordinates.lean](CircularLaw/OrderedCoordinates.lean), [OrderedBlockGeometry.lean](CircularLaw/OrderedBlockGeometry.lean) | Literal decreasing-norm permutation, including ties; equal-size top/tail blocks, disjointness and separation from the ordered-vector gap | Block construction in `lem:equal-block` |
| [EqualBlockScale.lean](CircularLaw/EqualBlockScale.lean), [EqualBlockLogScale.lean](CircularLaw/EqualBlockLogScale.lean), [EqualBlockConstants.lean](CircularLaw/EqualBlockConstants.lean) | Exact floor `m0`, quotient rounding and density bounds; absolute large-block threshold, one-half probability and logarithmic rate; common positive constants for both regimes | Parameters in `lem:equal-block` |
| [EqualBlockOrderedEstimate.lean](CircularLaw/EqualBlockOrderedEstimate.lean), [EqualBlock.lean](CircularLaw/EqualBlock.lean) | Both ordered-vector estimates, uniform witness-event inclusion, literal retained shifted matrix action, exact full-matrix marginalization, and eventual compatibility with the polylogarithmic degree range | Full `lem:equal-block` |
| [WitnessSliceCount.lean](CircularLaw/WitnessSliceCount.lean), [FiniteDisjointEvents.lean](CircularLaw/FiniteDisjointEvents.lean), [RowWitnessProbability.lean](CircularLaw/RowWitnessProbability.lean) | Exact singleton support count, disjoint event sum, and actual unique-coordinate and block-witness probabilities | Section 4 witness laws |
| [SingletonWitnessLower.lean](CircularLaw/SingletonWitnessLower.lean), [RowWitnessBounds.lean](CircularLaw/RowWitnessBounds.lean) | Lower witness probabilities from the checked one- and two-coordinate laws; dependence within each fixed-size support is retained | Section 4 witness means |
| [IndependentLowerTail.lean](CircularLaw/IndependentLowerTail.lean), [WitnessCountTail.lean](CircularLaw/WitnessCountTail.lean) | Laplace bound with the sum of the actual coordinate probabilities; half-mean and four-fifths-mean lower tails; unique-coordinate and equal-block row counts | Section 4 witness Chernoff estimates |
| [DisjointSetPairs.lean](CircularLaw/DisjointSetPairs.lean), [BinomialEntropy.lean](CircularLaw/BinomialEntropy.lean) | Exact `choose(n,t)*choose(t,s)` pair count, including impossible sizes; weighted binomial theorem proves the `(e*n/t)^t` bound | Section 4 witness entropy |
| [UniformWitnessFailure.lean](CircularLaw/UniformWitnessFailure.lean), [UniqueWitnessFailure.lean](CircularLaw/UniqueWitnessFailure.lean), [UniformWitnessEntropy.lean](CircularLaw/UniformWitnessEntropy.lean) | Uniform failure bounds over actual disjoint coordinate pairs, exact restriction to eligible rows outside their union, and the source form `exp(-c*d*s+2*s*log(e*n/s))` for equal blocks | Section 4, `eq:unique-witness-chernoff` and `eq:W-s-failure` |
| [UniqueWitnessAction.lean](CircularLaw/UniqueWitnessAction.lean), [OrderedPrefix.lean](CircularLaw/OrderedPrefix.lean), [SteepWitnessExclusion.lean](CircularLaw/SteepWitnessExclusion.lean) | Actual top coordinate sets and their norm bounds; exact shifted row estimate; a uniform witness event simultaneously excludes every ordered-jump vector and allowed constant shift from the retained matrix kernel | Section 4, mechanism in `eq:T0-exclusion` |
| [WitnessDegreeRates.lean](CircularLaw/WitnessDegreeRates.lean) | Degree entropy absorption; literal floor-scale failure `exp(-(binomialHalfRate/1600)*n)`; eventual compatibility with logarithmic lower and polylogarithmic upper degree bounds; fixed `Z0*sqrt(d)` shift window | Section 4, floor-scale branch of `eq:witness-scale-failures` |
| [FirstSteepScale.lean](CircularLaw/FirstSteepScale.lean), [FirstScaleWitnessFailure.lean](CircularLaw/FirstScaleWitnessFailure.lean) | Literal ceiling `n1`, density and entropy bounds; actual full-matrix witness failure `exp(-(binomialHalfRate/4)*n/sqrt(d))` throughout the source degree band | Section 4, ceiling-scale branch of `eq:witness-scale-failures` |
| [SteepScales.lean](CircularLaw/SteepScales.lean), [KernelCodimension.lean](CircularLaw/KernelCodimension.lean), [SteepScaleGeometry.lean](CircularLaw/SteepScaleGeometry.lean) | Literal floor stride, least starting exponent, final exponent and terminal ceiling; both codimensions; starting exponent precedes the final exponent; every actual pair has the required size, ratio, density and eligible-row bounds | Section 4, `eq:kernel-codimension` through `eq:sr-tr` |
| [SteepWitnessEntropy.lean](CircularLaw/SteepWitnessEntropy.lean), [SteepStrideRates.lean](CircularLaw/SteepStrideRates.lean), [SteepDimensionRates.lean](CircularLaw/SteepDimensionRates.lean) | Exact pair entropy absorbed at every source scale; finite scale union bound; logarithmic degree growth and polylogarithmic dimension bounds discharge all finite conditions and the scale-count prefactor | Section 4, `eq:E0-failure` |
| [SourceSteepClasses.lean](CircularLaw/SourceSteepClasses.lean), [SourceSteepWitness.lean](CircularLaw/SourceSteepWitness.lean), [SourceSteepExclusion.lean](CircularLaw/SourceSteepExclusion.lean) | Actual recursive `T0` classes and shifted class; full multiscale witness event; simultaneous shifted `T0` kernel exclusion and `exp(-(5*uniqueWitnessRate/2)*n/d^3)` probability bound, for both codimensions and all spectral shifts in the source window | Section 4, `eq:T0i`, `eq:T0r`, `eq:E0-failure` and `eq:T0-exclusion` |
| [OrderedNormAt.lean](CircularLaw/OrderedNormAt.lean), [OrderedNormStability.lean](CircularLaw/OrderedNormStability.lean) | One-based source order statistics; actual sorted moduli are stable under coordinatewise perturbations and constant shifts, with no assumption on sorting permutations | Section 4, ordered-coordinate arguments |
| [PermittedSteepShift.lean](CircularLaw/PermittedSteepShift.lean), [SourceStartingRank.lean](CircularLaw/SourceStartingRank.lean), [SourceVerySteepInclusion.lean](CircularLaw/SourceVerySteepInclusion.lean) | The actual shifted `T3` inclusion into `VL`, retaining `0.9`, minimal starting rank, literal floor normal rank and nonzero vectors; both codimensions | Section 4, `eq:T3-shift-inclusion` through `eq:T3-in-VL` |
| [SourceRemainingClasses.lean](CircularLaw/SourceRemainingClasses.lean), [SourceNoSteep.lean](CircularLaw/SourceNoSteep.lean) | Literal `T1`, `T2`, almost-constant and `S(t)` classes; shifted-union equality; first applicable recursive jump; a nonzero vector with zero first-scale modulus belongs to `T0` or `T3`; a large first-to-third-scale gap belongs to the full steep union | Section 4 source classes and deterministic alternatives |
| [AlmostConstantGeometry.lean](CircularLaw/AlmostConstantGeometry.lean), [AlmostConstantReductionFinite.lean](CircularLaw/AlmostConstantReductionFinite.lean), [AlmostConstantRanks.lean](CircularLaw/AlmostConstantRanks.lean), [AlmostConstantReduction.lean](CircularLaw/AlmostConstantReduction.lean) | Count-based center bounds and translated-tail bound; both positive-tail and zero-tail cases; exact floor `n0`, all valid ranks and uniform lower-band compatibility; full named deterministic almost-constant reduction | `lem:almost-constant-reduction` |
| [LowerBandEventually.lean](CircularLaw/LowerBandEventually.lean), [UniformSourceKernelConditions.lean](CircularLaw/UniformSourceKernelConditions.lean), [UniformSourceKernel.lean](CircularLaw/UniformSourceKernel.lean) | One threshold covers every degree in the literal lower band, both codimensions and all deterministic retained sets; full multiscale witness failure and spectral-window `T0` probability, and permitted `T3` inclusion | Uniformity in Section 4 |
| [IndependentUpperTail.lean](CircularLaw/IndependentUpperTail.lean), [RowLoadProbability.lean](CircularLaw/RowLoadProbability.lean), [SmallSetEntropy.lean](CircularLaw/SmallSetEntropy.lean), [RowLoadFailure.lean](CircularLaw/RowLoadFailure.lean), [RowLoadRates.lean](CircularLaw/RowLoadRates.lean) | Exact support-load expectation, one-row Markov estimates, independent-row upper tail, entropy of the actual small-set families, and the uniform `exp(-c*n)` failure bound for the literal row-load event | Section 4, `eq:load-small-J` through `eq:load-failure` |
| [RowLoadSurvival.lean](CircularLaw/RowLoadSurvival.lean), [AlmostConstantRowAction.lean](CircularLaw/AlmostConstantRowAction.lean), [AlmostConstantRowSets.lean](CircularLaw/AlmostConstantRowSets.lean), [AlmostConstantLoadExclusion.lean](CircularLaw/AlmostConstantLoadExclusion.lean), [UniformAlmostConstantLoad.lean](CircularLaw/UniformAlmostConstantLoad.lean) | Literal four coordinate sets, surviving-row count `K-3*K/8-n3 >= n/2`, exact shifted row action, source `d/2` lower bound, and simultaneous almost-constant `S(12)` kernel exclusion for both codimensions and all shifts in the source window | Section 4, `eq:surviving-G`, `eq:almost-constant-row-lower` and the row-load exclusion |
| [SourceHomogeneity.lean](CircularLaw/SourceHomogeneity.lean), [SourceGradualNormalization.lean](CircularLaw/SourceGradualNormalization.lean), [SourceKernelBridge.lean](CircularLaw/SourceKernelBridge.lean) | Actual order-statistic scaling, homogeneity of every recursive steep class and the almost-constant class, the exact normalized gradual class and nonzero complex scalar cone, and the deterministic kernel alternative from class exclusions | Section 4, `def:gradual-class` and the deterministic end of `thm:kernel-compatibility`; its class-exclusion inputs are discharged by the full theorem below |
| [SteepStrideCubic.lean](CircularLaw/SteepStrideCubic.lean), [SourceCoordinateGrowth.lean](CircularLaw/SourceCoordinateGrowth.lean) | Cubic growth of the literal floor stride; terminal-ceiling modulus bound; backward recursive no-jump chain; weighted envelope and initial-modulus bound | LLTTY19 Lemma 4.2 input to Sections 4–5 |
| [SourceGradualCoordinates.lean](CircularLaw/SourceGradualCoordinates.lean), [CoordinateRanges.lean](CircularLaw/CoordinateRanges.lean) | Actual gradual `n^6` maximum and `d^(3/2)` tail; any sorting permutation including ties; canonical rounding and uniform degree-band threshold for both codimensions; full named coordinate-range lemma | Section 5, `lem:coordinate-ranges` |
| [GridBox.lean](CircularLaw/GridBox.lean), [SparseGridNet.lean](CircularLaw/SparseGridNet.lean), [SourceNetCoordinates.lean](CircularLaw/SourceNetCoordinates.lean), [SteepNetGrid.lean](CircularLaw/SteepNetGrid.lean), [SteepNetCardinality.lean](CircularLaw/SteepNetCardinality.lean) | Finite integer grid boxes and three-range coordinate families; exact small-set counts; normalized literal `T1/T2` coordinate ranges; error `d^(-3/2)`, ordered gap above `2/3`, zero moduli from the strict cutoff onward; separate constant grids and exact finite net cardinality bounds | Section 4, `eq:shifted-net-error` and geometry of the `T1/T2` nets |
| [SteepNetEntropy.lean](CircularLaw/SteepNetEntropy.lean), [SteepGridPolynomial.lean](CircularLaw/SteepGridPolynomial.lean), [SteepNetRanks.lean](CircularLaw/SteepNetRanks.lean), [SteepNetBudgets.lean](CircularLaw/SteepNetBudgets.lean), [SteepNetAbsorption.lean](CircularLaw/SteepNetAbsorption.lean), [SteepNetCardinalityFinite.lean](CircularLaw/SteepNetCardinalityFinite.lean), [SteepNetCardinalityUniform.lean](CircularLaw/SteepNetCardinalityUniform.lean) | Exact count entropy, literal rounded prefix densities and integer grid bounds; all support and prefix costs absorbed into the source coefficient seven; actual product net count at most `exp(7*n_next*log(d))`, with one dimension threshold for all degrees in the source lower band | Section 4, `eq:shifted-net-size` |
| [SourceSteepNetLemma.lean](CircularLaw/SourceSteepNetLemma.lean) | Closed steep-net dependency combining actual product counts, literal ordered gap at least `1-d^(-3/2)` and above `2/3`, strict support cutoff and separate component approximation for every normalized source `T1/T2` vector and permitted constant shift, uniformly over the degree band and both codimensions | LLTTY19 Lemma 4.5 input to Section 4 |
| [SteepNetMatrixError.lean](CircularLaw/SteepNetMatrixError.lean), [ShiftedSteepNetCover.lean](CircularLaw/ShiftedSteepNetCover.lean), [SteepKernelNormalization.lean](CircularLaw/SteepKernelNormalization.lean), [SteepNetUnion.lean](CircularLaw/SteepNetUnion.lean), [SteepNetSmallBall.lean](CircularLaw/SteepNetSmallBall.lean) | Actual row and rectangular L2 error `2*(1+Z0)*sqrt(n/d)`; separate component approximants; normalization of every shifted source kernel vector; finite net union bound with witness failure separate; both checked equal-block estimates applied to every actual net member | Section 4, `eq:shifted-net-matrix-error` and finite steps of `eq:T1-exclusion`, `eq:T2-exclusion` |
| [SteepNetFit.lean](CircularLaw/SteepNetFit.lean), [SteepNetProbabilityRates.lean](CircularLaw/SteepNetProbabilityRates.lean), [UniformSteepNetExclusion.lean](CircularLaw/UniformSteepNetExclusion.lean) | Literal rounded rank ordering and block fits; both actual approximation radii fit the checked equal-block estimates; actual net entropy absorbed into both small-ball exponents; witness failures combined separately; full T1/T2 kernel exclusions with positive absolute rates and a proved admissible `a3` range, uniformly over the source band, both codimensions, every retained set and fixed-window spectral shift | Section 4, full `eq:T1-exclusion` and `eq:T2-exclusion` |
| [KernelProbabilityAssembly.lean](CircularLaw/KernelProbabilityAssembly.lean), [KernelCompatibility.lean](CircularLaw/KernelCompatibility.lean) | Exact source kernel event; four-event failure union; all checked exponential rates imply the explicit `4/n` failure bound; fixed positive `a3` range and absolute logarithmic lower constant; literal very-steep class and nonzero complex scalar cone contain the nonzero retained kernel with probability at least `1-4/n` | Full named `thm:kernel-compatibility`, including uniformity over both codimensions |
| [IntegerGibbs.lean](CircularLaw/IntegerGibbs.lean), [CountableEntropy.lean](CircularLaw/CountableEntropy.lean), [WeightEntropy.lean](CircularLaw/WeightEntropy.lean) | Full integer-law entropy bound `H <= 2+log(4)+log(1+D)`; infinite-support and infinite-dispersion cases; finite dispersion implies summable entropy; dispersion equals the independent-copy expected distance; transfer to integer random variables on arbitrary probability spaces | Full named `lem:weight-entropy` |
| [EntropyCancellation.lean](CircularLaw/EntropyCancellation.lean), [FiniteWeightEntropy.lean](CircularLaw/FiniteWeightEntropy.lean), [DyadicWeightEntropy.lean](CircularLaw/DyadicWeightEntropy.lean) | Uniform-coordinate integer law with coincident bins aggregated; exact identification with the actual row-profile dyadic dispersion; entropy penalty and exponential cancellation for at least half the rows, with the counting/compression inequality explicit | Section 5, analytic step in `eq:entropy-dispersion-cancel` |
| [MultinomialEntropy.lean](CircularLaw/MultinomialEntropy.lean), [IntegerHistogram.lean](CircularLaw/IntegerHistogram.lean), [DyadicHistogramEntropy.lean](CircularLaw/DyadicHistogramEntropy.lean) | Weighted multinomial theorem gives the exact factorial entropy bound, including zero-size bins and zero total count; actual integer histogram counts sum to dimension; the exponent equals dimension times the uniform-law entropy; the actual dyadic bins are exactly `[2^b,2^(b+1))`; their factorial ratio has the entropy bound and exponential dispersion cancellation | Section 5, the second inequality in `eq:factorial-entropy` and its dyadic-bin cancellation |
| [ProfileFactorialEntropy.lean](CircularLaw/ProfileFactorialEntropy.lean) | Actual bin sizes equal sums of actual part sizes; part factorial product regrouped exactly by dyadic bin; local bin compression implies the global part-to-bin factorial comparison, entropy inequality and dispersion cancellation | `eq:factorial-entropy` and `eq:entropy-dispersion-cancel`; canonical compression is proved below |
| [FourFamilyEntropy.lean](CircularLaw/FourFamilyEntropy.lean), [ProfileLogGeometry.lean](CircularLaw/ProfileLogGeometry.lean) | Four-family geometric tails have uniformly bounded entropy; exact log formulas for the source truncated weights; size-height geometry implies same-bin size decay along creation orders | LLTTY19 Lemma 7.2 geometric argument |
| [ProfileBinCompression.lean](CircularLaw/ProfileBinCompression.lean), [ProfileSmallBinMass.lean](CircularLaw/ProfileSmallBinMass.lean) | Local bin factorial compression with constant `4096`; arbitrary selected parts smaller than `T` in one bin have total mass at most `512*T`; coordinate union cardinality equals the sum of its part sizes | `eq:factorial-compression` and `eq:small-bin-mass`, from explicit creation-order geometry |
| [CanonicalBinCompression.lean](CircularLaw/CanonicalBinCompression.lean) | Supplies the geometry for the actual canonical and ordered canonical partitions; closed local compression, actual coordinate-union cutoff bound, and factorial entropy/dispersion cancellation | Both assertions in part (iii) of `prop:LLTTY-package`; closed `eq:factorial-entropy` and `eq:entropy-dispersion-cancel` for the canonical profile |
| [PartAssignmentCounting.lean](CircularLaw/PartAssignmentCounting.lean), [PartLevelCounting.lean](CircularLaw/PartLevelCounting.lean) | Exact fixed-size assignment count and level-choice product, including empty parts | Combinatorial count in `eq:class-cardinality` |
| [CoordinateMultiset.lean](CircularLaw/CoordinateMultiset.lean), [CoordinateClassRestriction.lean](CircularLaw/CoordinateClassRestriction.lean), [CanonicalClassInvariants.lean](CircularLaw/CanonicalClassInvariants.lean), [CanonicalClassCardinality.lean](CircularLaw/CanonicalClassCardinality.lean) | Coordinate-multiset equality equals permutation; actual part data are class-invariant; injective canonical part/value encoding proves the full class-size formula for arbitrary restricted approximation families; subfamily class count is monotone with finiteness explicit | Class-size and restriction assertions in part (ii) of `prop:LLTTY-package`; the `e^n` class-count bound is proved below |
| [CanonicalClassEntropy.lean](CircularLaw/CanonicalClassEntropy.lean) | Combines the actual class-size bound with canonical factorial entropy and dispersion cancellation; multiplying by the actual inverse truncated weights leaves the source height/weight product | Section 5 class-sum entropy reduction; probability sums over gradual nets remain open |
| [BlockMultisetCounting.lean](CircularLaw/BlockMultisetCounting.lean), [BlockMultisetEntropy.lean](CircularLaw/BlockMultisetEntropy.lean) | Injective block-multiset class encoding, exact stars-and-bars counts, and real size/alphabet entropy caps, including empty blocks | Class-count inputs to part (ii) of `prop:LLTTY-package` |
| [GradualClassBlocks.lean](CircularLaw/GradualClassBlocks.lean), [GradualClassAlphabets.lean](CircularLaw/GradualClassAlphabets.lean), [GradualClassCounting.lean](CircularLaw/GradualClassCounting.lean), [GradualClassEntropyFormula.lean](CircularLaw/GradualClassEntropyFormula.lean), [UniformGradualClassCount.lean](CircularLaw/UniformGradualClassCount.lean) | Actual gradual approximation families are finite; four rank-block alphabets and entropy costs give at most `exp(n)` multiset classes, also for every restricted family, uniformly in the standing lower band, both codimensions and the full stated scale range | Completes the class-count assertions in part (ii) in the manuscript's setting, with `0<a3<=1/65536` |
| [ApproximationRefinement.lean](CircularLaw/ApproximationRefinement.lean), [LevelSliceCounts.lean](CircularLaw/LevelSliceCounts.lean), [LevelRefinement.lean](CircularLaw/LevelRefinement.lean), [FloorGridCover.lean](CircularLaw/FloorGridCover.lean), [RefinementSpread.lean](CircularLaw/RefinementSpread.lean), [RefinementMassDichotomy.lean](CircularLaw/RefinementMassDichotomy.lean), [SeparatedOrderDichotomy.lean](CircularLaw/SeparatedOrderDichotomy.lean) | Exact successive floor refinement, level survival thresholds, unique majority levels, factor-eight prefix-mass transfer, nine-cell greedy spread bound, and the actual one-step spread/shrinking inequality; the separated cohorts are explicit hypotheses | Deterministic inputs to part (i) of `prop:LLTTY-package`; their gradual inputs and full decomposition are supplied below |
| [RankQuantiles.lean](CircularLaw/RankQuantiles.lean), [PlanarQuantileCohorts.lean](CircularLaw/PlanarQuantileCohorts.lean), [GradualRefinementDichotomy.lean](CircularLaw/GradualRefinementDichotomy.lean), [SourceRefinementFamilies.lean](CircularLaw/SourceRefinementFamilies.lean), [AccumulatedShrinkage.lean](CircularLaw/AccumulatedShrinkage.lean), [LowHeightCoordinates.lean](CircularLaw/LowHeightCoordinates.lean), [GradualLevelAccumulation.lean](CircularLaw/GradualLevelAccumulation.lean), [GradualDecomposition.lean](CircularLaw/GradualDecomposition.lean) | Actual quantile cohorts from gradual nonconcentration; literal `Ku` and `Pv`; uniform one-step dichotomy; accumulated factor-two contractions; coordinate mass in actual high-height parts; full gradual decomposition with positive absolute constants | Closes part (i) of `prop:LLTTY-package` in the standing manuscript setting, uniformly in every `v>=5` |
| [ProfileCutoffProduct.lean](CircularLaw/ProfileCutoffProduct.lean), [SourceK1Product.lean](CircularLaw/SourceK1Product.lean), [IntegerOrderQuantiles.lean](CircularLaw/IntegerOrderQuantiles.lean), [ProfileK2Separation.lean](CircularLaw/ProfileK2Separation.lean), [SourceK2Separation.lean](CircularLaw/SourceK2Separation.lean) | Actual cutoff/spread masses and exact height/weight product; floor-corrected K1 decay and class entropy consequence; integer quantiles and actual small-bin bound; both K2 tails and degree-power gap, with a uniform dimension threshold | Closes part (iv) of `prop:LLTTY-package` in the standing manuscript setting |
| [Binomial.lean](CircularLaw/Binomial.lean) | Proves the occupancy Laplace transform, multiplicative Chernoff lower tail, disjoint-large-part count, multinomial failure estimate `d^(1/3)*exp(-c*d^(2/3))`, and eventual absorption of the prefactor | Section 3, profile good-event failure bound |
| [ProfileEstimator.lean](CircularLaw/ProfileEstimator.lean) | Exact actual and truncated weights; the sample-index estimator equals the minimum over visited parts; good-event comparison; part-mass averaging; dyadic geometric mean; first averaged-estimator conclusion with explicit constants and an absolute degree threshold | Section 3, first conclusion of `prop:averaged-profile` |
| [ProfileRange.lean](CircularLaw/ProfileRange.lean) | Truncated-weight bounds from positive heights bounded by dimension; dyadic support diameter; compatibility with logarithmic degree; uniform eventual estimator bound under the main degree assumptions | Sections 2–3, weight range and large logarithmic constant |
| [ClosedFloorCells.lean](CircularLaw/ClosedFloorCells.lean), [LargeSelectedLevel.lean](CircularLaw/LargeSelectedLevel.lean), [WeightHeightBounds.lean](CircularLaw/WeightHeightBounds.lean), [RepeatedValueWeight.lean](CircularLaw/RepeatedValueWeight.lean), [SourceClusterLowTail.lean](CircularLaw/SourceClusterLowTail.lean) | Closed-disk nine-cell bound; actual last nonempty level chunk; exact repeated-value part mass and truncated weight; clustered low-tail mass `delta/36` | Low-weight half of part (v) of `prop:LLTTY-package` |
| [ProfileHighHeightBins.lean](CircularLaw/ProfileHighHeightBins.lean), [HighHeightTail.lean](CircularLaw/HighHeightTail.lean), [SqrtHeightCutoff.lean](CircularLaw/SqrtHeightCutoff.lean), [SourcePvHighTail.lean](CircularLaw/SourcePvHighTail.lean), [SourcePvSeparation.lean](CircularLaw/SourcePvSeparation.lean) | Actual high-height mass; stronger upper cutoff via bounded actual small-bin interval; upper-tail mass `cP*a3/4`; manuscript separation hypothesis and integer gap, uniformly in every scale and codimension | Closes part (v) of `prop:LLTTY-package` |
| [SourceLLTTYPackage.lean](CircularLaw/SourceLLTTYPackage.lean) | All five parts with common positive constants, actual families and classes, literal hypotheses and a single uniform dimension threshold | Full named `prop:LLTTY-package` |
| [TailDispersion.lean](CircularLaw/TailDispersion.lean), [SourceProfileDispersion.lean](CircularLaw/SourceProfileDispersion.lean) | Two separated probability tails give pair dispersion; actual K2 and clustered-Pv dispersion bounds, uniformly in the standing degree band | Section 5 branch estimates |
| [ProfileMeanPowers.lean](CircularLaw/ProfileMeanPowers.lean), [CanonicalProfileStatistics.lean](CircularLaw/CanonicalProfileStatistics.lean) | Exact geometric-mean power product; retained-row cost bounded by `(n*sqrt(d))^L`; equality of raw and ordered canonical profile statistics | Section 5 class estimates |
| [ClassRowEnergy.lean](CircularLaw/ClassRowEnergy.lean), [SourceClassRowEnergy.lean](CircularLaw/SourceClassRowEnergy.lean) | Actual class cardinality times the retained-row weight/dispersion factor; K1 product decay and K2/Pv exponential dispersion decay at `K=n-L`, uniformly over both codimensions | Supporting class estimates for `thm:row-slice-structural` |
| [FixedNetSlice.lean](CircularLaw/FixedNetSlice.lean), [FullMatrixFixedNet.lean](CircularLaw/FullMatrixFixedNet.lean) | Fixed-vector norm small ball at radius `R*log(d)*sqrt(d*n)/k`; exact transport to the full matrix law for every deterministic retained set and vector shift, including the empty set | Supporting estimates for `lem:net-reduction` |
| [CanonicalClassStatistics.lean](CircularLaw/CanonicalClassStatistics.lean) | Equal actual part sizes, masses, heights and kinds on a coordinate-multiset class; equality of geometric mean, dispersion and fixed-vector probability estimate | Section 5 class invariance |
| [CanonicalClassProbability.lean](CircularLaw/CanonicalClassProbability.lean), [FixedNetSplit.lean](CircularLaw/FixedNetSplit.lean), [CanonicalClassSplit.lean](CircularLaw/CanonicalClassSplit.lean) | Actual class probability sums and event union; separate dispersion and profile-exception terms; K1/K2/Pv class bounds at the literal retained row count, uniformly in the standing band | Section 5 class probability estimates |
| [CoordinateClassSummation.lean](CircularLaw/CoordinateClassSummation.lean), [CanonicalFamilyProbability.lean](CircularLaw/CanonicalFamilyProbability.lean) | Exact regrouping of the family sum by represented classes; class sizes sum to the family size; uniform `exp(n)` class-count cost and exact vector-count cost for the exception term | Section 5 family probability sums |
| [TwoAlphabetCounting.lean](CircularLaw/TwoAlphabetCounting.lean), [GradualNetCounting.lean](CircularLaw/GradualNetCounting.lean), [GradualNetEntropy.lean](CircularLaw/GradualNetEntropy.lean) | Exact top-position and two-alphabet count for actual gradual approximations; uniform `exp(128*n*d^(1/3))` cardinality bound under the discretization logarithm budget | Section 5 crude net count |
| [StructuralParameters.lean](CircularLaw/StructuralParameters.lean), [StructuralDiscretization.lean](CircularLaw/StructuralDiscretization.lean), [StructuralNetUnion.lean](CircularLaw/StructuralNetUnion.lean) | Literal codimension-dependent growth, radius, cluster fraction and floor exponent; terminal radius comparison and scale-range fit; actual union cardinality at most `vL*exp(128*n*d^(1/3))` | Section 5 terminal scale and `eq:crude-net-count` |
| [ProfileExceptionCost.lean](CircularLaw/ProfileExceptionCost.lean), [ProfileExceptionUnion.lean](CircularLaw/ProfileExceptionUnion.lean), [SourceTerminalProbability.lean](CircularLaw/SourceTerminalProbability.lean) | Conditioning and row-factor bounds; profile-exception decay after all terminal scales and the displayed scalar-grid prefactor; actual K1/K2 family sums with scale range and exception cost discharged | Section 5 profile-exception term and branch probability inputs |
| [MissingRowCost.lean](CircularLaw/MissingRowCost.lean), [LogarithmicNetCost.lean](CircularLaw/LogarithmicNetCost.lean), [StructuralBranchEnergy.lean](CircularLaw/StructuralBranchEnergy.lean) | Actual missing-row factor at most `exp(n)`; row cost retaining `log(log(d))`; K1 logarithmic and K2 degree-power decay after the class count, conditioning and missing-row costs | Section 5 K1/K2 energy absorption |
| [FiniteProbabilitySupremum.lean](CircularLaw/FiniteProbabilitySupremum.lean), [SourceSpreadProbability.lean](CircularLaw/SourceSpreadProbability.lean), [SourceSpreadScaleSum.lean](CircularLaw/SourceSpreadScaleSum.lean) | Each shift supremum is attained; the two mass cases cover the actual spread family; the complete `4<=u<=vL` sum of fixed-vector suprema is at most `exp(-(sourceK1DecayExponent(a3)/4)*n*log(d))`, also after the displayed `2*d^2` prefactor | Section 5 `eq:Ku-total` |
| [TerminalClusterParameters.lean](CircularLaw/TerminalClusterParameters.lean), [TerminalClusterBudgets.lean](CircularLaw/TerminalClusterBudgets.lean), [TerminalPvHypotheses.lean](CircularLaw/TerminalPvHypotheses.lean) | Literal `deltaL`, the terminal floor loss and logarithmic separation budget; every clustered-Pv hypothesis follows uniformly from the source degree band and codimension | Section 5 `eq:delta-v-growth` and `eq:Pv-hypotheses` |
| [TerminalPvEnergy.lean](CircularLaw/TerminalPvEnergy.lean), [TerminalPvProbability.lean](CircularLaw/TerminalPvProbability.lean), [TerminalPvPrefactor.lean](CircularLaw/TerminalPvPrefactor.lean) | Actual clustered terminal family with the strict source cluster inequality; full sum of shift suprema bounded by `exp(-(sourcePvDecayRate(a3)/4)*n*deltaL*vL)+exp(-(averagedProfileRate/8)*n*d^(2/3))`, including the displayed `2*d^2` prefactor | Section 5 `eq:clustered-Pv` and `eq:Pv-clustered-prob` |
| [CenteredCanonicalApproximation.lean](CircularLaw/CenteredCanonicalApproximation.lean), [ScalarMeanGrid.lean](CircularLaw/ScalarMeanGrid.lean) | Literal mean of floor errors, strict component ranges, zero-sum centered error and Euclidean bound; actual finer mean grid has at most `d^2` values | Section 5 `eq:net-w-alpha` and `eq:alpha-rounding` |
| [CenteredSliceAction.lean](CircularLaw/CenteredSliceAction.lean), [CanonicalNetKernelCover.lean](CircularLaw/CanonicalNetKernelCover.lean) | Actual retained centered-norm event, exact shifted-kernel identity and covering by the canonical image and scalar grid; the fixed spectral window is absorbed into the source `R*log(d)*sqrt(d*n)/k` radius | Deterministic part of `lem:net-reduction` |
| [CanonicalKernelProbabilityReduction.lean](CircularLaw/CanonicalKernelProbabilityReduction.lean), [TerminalKernelProbability.lean](CircularLaw/TerminalKernelProbability.lean) | Continuous kernel probabilities reduce to actual sums of shift suprema with at most the displayed `2*d^2` prefactor; the spread union and clustered terminal family have their source decays plus the explicit retained centered-norm failure probability | Conditional probability reduction for `lem:net-reduction` and `thm:row-slice-structural` |
| [SourceNormalCoordinates.lean](CircularLaw/SourceNormalCoordinates.lean), [StructuralNormalRadius.lean](CircularLaw/StructuralNormalRadius.lean), [StructuralKernelAlternatives.lean](CircularLaw/StructuralKernelAlternatives.lean) | Literal floor normal-rank modulus at most `d^16`, uniform structural radius comparison, cluster rescaling and exact structural alternatives; the assembled failure bound retains the actual norm failure probability | `eq:radius-comparison` and conditional assembly of `thm:row-slice-structural` |
| [StructuralFailureBudgets.lean](CircularLaw/StructuralFailureBudgets.lean) | Each terminal decay is uniformly at most `n^-2`; the exact structural alternatives have probability at least `1-5/n` conditional on the actual retained norm failure being at most `n^-100` | Conditional final probability absorption for `thm:row-slice-structural` |
| [WeightedSliceLaplace.lean](CircularLaw/WeightedSliceLaplace.lean), [WeightedMatrixLaplace.lean](CircularLaw/WeightedMatrixLaplace.lean) | Weighted exact-slice generating function, both tilt signs via the literal complement law, actual weighted mean, independent-row exponential moments and squared-weight variance proxy | Concentration input to `prop:restricted-norm` |
| [WeightedMatrixConcentration.lean](CircularLaw/WeightedMatrixConcentration.lean), [SignedMatrixConcentration.lean](CircularLaw/SignedMatrixConcentration.lean) | Checked finite Markov step, two-sided bounded-weight concentration, signed coefficient split and tail `4*exp(-t^2/(16*v+8*K*t))`; the variance upper bound and maximum weight are deterministic inputs | Light-term concentration infrastructure for `prop:restricted-norm` |
| [LightCoupleBounds.lean](CircularLaw/LightCoupleBounds.lean), [LightCoupleConcentration.lean](CircularLaw/LightCoupleConcentration.lean) | Actual rank-one light coefficients, squared-weight and mean bounds, and tail `4*exp(-B*n/32)` at threshold `d/sqrt(N)+B*sqrt(N)` | Light-term input to `prop:restricted-norm` |
| [RowSliceEdgeCounts.lean](CircularLaw/RowSliceEdgeCounts.lean), [RowSliceEdgeTails.lean](CircularLaw/RowSliceEdgeTails.lean) | Actual support-intersection edge counts, exact mean, Poisson exponential moments and fixed-set logarithmic bad-event bound `exp(-c/2)` | Fixed-set discrepancy input to `prop:restricted-norm` |
| [EdgeDiscrepancyEntropy.lean](CircularLaw/EdgeDiscrepancyEntropy.lean), [RowSliceDiscrepancy.lean](CircularLaw/RowSliceDiscrepancy.lean), [RowSliceDiscrepancyUnion.lean](CircularLaw/RowSliceDiscrepancyUnion.lean) | Actual fixed-size set counts, increasing entropy cost, and simultaneous discrepancy with parameters `exp(2)`, `2*(beta+4)` and failure at most `n^-beta` | Checked discrepancy input of LLY26a Lemma 4.7 |
| [MatrixDiscrepancy.lean](CircularLaw/MatrixDiscrepancy.lean), [RowSliceMatrixDiscrepancy.lean](CircularLaw/RowSliceMatrixDiscrepancy.lean) | Literal real rectangular matrix, exact edge and column count bridges, row sums, discrepancy equivalence and deterministic edge bounds from row/column sums | Exact matrix conditions for the heavy-term argument |
| [RowSliceColumnBounds.lean](CircularLaw/RowSliceColumnBounds.lean), [RowSliceNormEvents.lean](CircularLaw/RowSliceNormEvents.lean) | All columns bounded by `9*d` with failure at most `n*exp(-9*d)`; joint degree and discrepancy failure at most `n^-A` under `(A+2)*log(n)<=9*d` | Probability inputs to the completed restricted-norm proposition |
| [NormDyadicLevels.lean](CircularLaw/NormDyadicLevels.lean), [NormDyadicMass.lean](CircularLaw/NormDyadicMass.lean), [NormHeavyDyadicCover.lean](CircularLaw/NormHeavyDyadicCover.lean) | Complete coordinate-level partition including small and zero coordinates, exact finite regrouping, total mass at most five for unit vectors, and the actual heavy bilinear sum bounded by its level edge costs | Checked heavy-pair cover |
| [NormDyadicSums.lean](CircularLaw/NormDyadicSums.lean), [NormHeavyLevelRatios.lean](CircularLaw/NormHeavyLevelRatios.lean), [NormHeavyDegreeSums.lean](CircularLaw/NormHeavyDegreeSums.lean), [NormHeavyEntropy.lean](CircularLaw/NormHeavyEntropy.lean) | Finite increasing and reciprocal geometric budgets, exact matrix edge-ratio normalization, the first two heavy-case sums and the literal discrepancy logarithm bridge | Checked heavy-case inputs |
| [NormHeavyLargeRatio.lean](CircularLaw/NormHeavyLargeRatio.lean), [NormHeavySmallMass.lean](CircularLaw/NormHeavySmallMass.lean), [NormHeavyModerateMass.lean](CircularLaw/NormHeavyModerateMass.lean), [NormHeavyCaseAssembly.lean](CircularLaw/NormHeavyCaseAssembly.lean), [NormHeavySquare.lean](CircularLaw/NormHeavySquare.lean) | All five case sums, exhaustive cover of the oriented pairs, exact transpose conditions and full square heavy bilinear bound with a dimension-independent constant | Deterministic heavy-term estimate |
| [NormRectangularPadding.lean](CircularLaw/NormRectangularPadding.lean), [NormPaddingDiscrepancy.lean](CircularLaw/NormPaddingDiscrepancy.lean), [NormHeavyRectangular.lean](CircularLaw/NormHeavyRectangular.lean), [RowSliceHeavyBound.lean](CircularLaw/RowSliceHeavyBound.lean) | Literal zero-row padding preserves edge counts, degree caps, discrepancy and squared vector mass; full rectangular heavy bound and actual simultaneous heavy event with polynomial failure | Rectangular heavy input to `prop:restricted-norm` |
| [NormLatticeCardinality.lean](CircularLaw/NormLatticeCardinality.lean), [NormLatticeRounding.lean](CircularLaw/NormLatticeRounding.lean), [NormLatticeNet.lean](CircularLaw/NormLatticeNet.lean), [NormMeanProjection.lean](CircularLaw/NormMeanProjection.lean) | Actual unit-ball quarter-net with at most `128^n` points, coordinate rounding cover, norm contraction under mean removal and the projected zero-sum net | Constructed finite nets for the norm proof |
| [NormFiniteNetReduction.lean](CircularLaw/NormFiniteNetReduction.lean), [RowSliceLightNet.lean](CircularLaw/RowSliceLightNet.lean), [RowSliceRealNorm.lean](CircularLaw/RowSliceRealNorm.lean), [NormRealComplexTransfer.lean](CircularLaw/NormRealComplexTransfer.lean) | Simultaneous light bound over actual net pairs, finite-net operator reduction, polynomial real norm tail and checked transfer to complex vectors | Closed norm probability assembly |
| [RestrictedNormTheorem.lean](CircularLaw/RestrictedNormTheorem.lean), [RestrictedNormRetained.lean](CircularLaw/RestrictedNormRetained.lean) | Full named restricted-norm proposition with one finite positive constant for threshold and norm; actual retained centered norm failure at most `n^-100` under `103*log(n)<=9*d` | `prop:restricted-norm` proved; norm input to canonical net reduction and structural kernel bounds |
| [RestrictedNormUniform.lean](CircularLaw/RestrictedNormUniform.lean), [NetReductionTheorem.lean](CircularLaw/NetReductionTheorem.lean) | Uniform retained norm tail supplies the full source net-reduction conclusions for every gradual subfamily: finite canonical image, class counts and cardinalities, kernel probability bound, and crude union count | `lem:net-reduction` proved |
| [RetainedRowOrthogonality.lean](CircularLaw/RetainedRowOrthogonality.lean), [StructuralKernelTheorem.lean](CircularLaw/StructuralKernelTheorem.lean) | Actual conjugated-row span orthogonality equals the shifted matrix kernel; fixed constants and a uniform source-band threshold give the exact structural alternatives with probability at least `1-5/n` | `thm:row-slice-structural` proved |
| [StandardComplexGaussian.lean](CircularLaw/StandardComplexGaussian.lean), [ComplexGaussianLinearForm.lean](CircularLaw/ComplexGaussianLinearForm.lean) | Actual image of independent real Gaussians with variance one half; real and imaginary marginals, independence, moments, characteristic function, and exact laws of all real linear forms | Supporting normalization for `prop:Gaussian-anti-clustering` |
| [ProjectedComplexGaussian.lean](CircularLaw/ProjectedComplexGaussian.lean), [GaussianInnerLaw.lean](CircularLaw/GaussianInnerLaw.lean) | Independent coordinate product, joint Gaussian vector, continuous actual orthogonal projection, retained shifted kernel, and exact Hermitian-form and projected-coordinate-difference laws including zero scales | Supporting projected Gaussian laws for `prop:Gaussian-anti-clustering` |
| [ComplexGaussianDensity.lean](CircularLaw/ComplexGaussianDensity.lean), [ProjectedGaussianSmallBall.lean](CircularLaw/ProjectedGaussianSmallBall.lean) | Exact density `exp(-norm(z)^2)/pi`; arbitrary-centre disk probability at most `(r/scale)^2` for each positive projected difference scale | Supporting pair small-ball estimate for the completed Gaussian proposition |
| [ComplexGaussianRadialTail.lean](CircularLaw/ComplexGaussianRadialTail.lean), [GaussianCorrelationSmallBall.lean](CircularLaw/GaussianCorrelationSmallBall.lean) | Polar integration proves the exact radial tail, including equality at the radius; the actual correlation definition forces a positive projected scale and gives the source fixed-pair estimate | LLTTY21 Lemma 4.8 input to `prop:Gaussian-anti-clustering` |
| [ClusterPairCounting.lean](CircularLaw/ClusterPairCounting.lean), [GaussianClusterAveraging.lean](CircularLaw/GaussianClusterAveraging.lean) | A disk containing `2*b` points contributes at least `2*b^2` close non-correlated ordered pairs; their actual expectation and Markov bound give failure at most `(s*n)^2/(2*b^2)` at the source radius whenever each retained index has at most `b` correlated neighbours | Averaging input to LLTTY21 Lemma 4.9 |
| [GreedyCorrelationClusters.lean](CircularLaw/GreedyCorrelationClusters.lean), [GaussianGreedyClusters.lean](CircularLaw/GaussianGreedyClusters.lean) | Actual maximal stars use cardinality then lexicographic indicator vectors; disjoint decreasing clusters exhaust the coordinates. The first small cluster gives the exceptional set, representative indices, the cluster-count bound, and the required neighbour bound on its complement. The actual Gaussian probability estimate now has this premise discharged | Full greedy construction and averaging conclusion of LLTTY21 Lemma 4.9 |
| [CoordinateDiskEvents.lean](CircularLaw/CoordinateDiskEvents.lean) | Disk-count events for continuous finite complex coordinates are closed and measurable, using compact centre projection; complements give actual success probability at least `1-(s*n)^2/(2*b^2)` | Measurability and probability of the Gaussian anti-clustering conclusion |
| [GaussianSourceParameters.lean](CircularLaw/GaussianSourceParameters.lean), [GaussianSourceAntiClustering.lean](CircularLaw/GaussianSourceAntiClustering.lean) | Literal `b=floor(L/2)`, `s=(L/n)^(3/2)/2`, and `beta=(L/(4*n))^3/4` give failure at most `9L/(8n)` for `L>=2`. An explicit exponent loss of 1024 absorbs the polynomial and logarithmic radius factors for every `0<L<=n`. The full measurable source conclusion follows with one common constant once the constructed exceptional set has the required size | Final parameter absorption in `prop:Gaussian-anti-clustering`; the exceptional-size premise is discharged below |
| [GaussianRepresentativeCombination.lean](CircularLaw/GaussianRepresentativeCombination.lean) | For `p+1` vectors and representatives, the `p` coordinate-difference constraints have a nonzero kernel; normalization gives unit Euclidean coefficients and equal representative coordinates. Combinations of actual projected Gaussian copies remain in the original orthogonal complement | Deterministic linear-algebra step in LLTTY21 Lemma 4.10; nonzero output follows from uniform non-flatness below |
| [GreedyCorrelationOwners.lean](CircularLaw/GreedyCorrelationOwners.lean), [ProjectedGaussianCopies.lean](CircularLaw/ProjectedGaussianCopies.lean) | Each exceptional coordinate has a unique earlier star and an actual correlated representative. The product sample law gives independent projected copies, exact marginals and pair tails, and joint Gaussian law | Actual sample space and representative lookup for the forbidden-vector construction |
| [CopyClusterCounting.lean](CircularLaw/CopyClusterCounting.lean), [GaussianCombinationClusters.lean](CircularLaw/GaussianCombinationClusters.lean), [GaussianGreedyCopyClusters.lean](CircularLaw/GaussianGreedyCopyClusters.lean) | Union, integration and Markov bound the probability that half the exceptional coordinates are far in any copy by `2*p*beta`. On the measurable complementary event, equal representative values give a disk of radius `p*alpha` containing more than half the actual exceptional set for a unit orthogonal combination. The actual copy count obeys `p<=2*n/L`, hence failure at most `1/64` and success at least `63/64` for the source parameters | Copy-closeness and large-cluster steps in the completed forbidden-vector argument |
| [GaussianCopiesCombinationLaw.lean](CircularLaw/GaussianCopiesCombinationLaw.lean) | Characteristic functions prove that a fixed raw combination has standard vector law scaled by the Euclidean coefficient norm, including zero coefficients. Projection commutes with the combination. Fixed unit combinations have the original projected law, with exact measurable-event probabilities | Distribution input for LLTTY21 Propositions 4.4/4.7 |
| [GaussianCoordinateTails.lean](CircularLaw/GaussianCoordinateTails.lean) | Actual projected coordinate scales are at most one; tails including zero scales are at most `exp(-r^2)`. Finite coefficient sets obey the union bound. One measurable event of probability at least `1-epsilon` bounds all coefficients of norm at most one in every coordinate by `sqrt(p)*sqrt(log(p*n/epsilon))` | Largest-coordinate bound supporting non-steepness; the full ordered-coordinate estimates remain open |
| [GaussianIsometryLaw.lean](CircularLaw/GaussianIsometryLaw.lean) | The adjoint of any complex linear isometric embedding maps the actual standard law to the smaller standard law. The literal orthonormal-coordinate map of any deterministic subspace has that law, and its norm equals the actual projection norm | Distribution input to the Gaussian projection small-ball estimate |
| [ComplexGaussianNormLaplace.lean](CircularLaw/ComplexGaussianNormLaplace.lean), [GaussianProjectionNorm.lean](CircularLaw/GaussianProjectionNorm.lean) | Exact exponential moments `(1-t)^(-r)` for `t<1`, integrability, and actual subspace squared-norm law. Markov gives the small-ball bound `(exp(1)*u/r)^r` for positive dimension and squared radius, and upper tail `2^r*exp(-u/2)` | Gaussian norm concentration supporting LLTTY21 Lemmas 4.3/4.5 |
| [GaussianCoordinateDeletion.lean](CircularLaw/GaussianCoordinateDeletion.lean) | The actual normal subspace vanishing on K loses at most `card(K)` dimensions. Its projected norm is controlled by the remaining coordinates; the Gaussian norm law bounds the event that all those coordinates are small | Coordinate-deletion step for LLTTY21 Lemma 4.3 |
| [OrderedNormContinuity.lean](CircularLaw/OrderedNormContinuity.lean), [GaussianOrderSmallBall.lean](CircularLaw/GaussianOrderSmallBall.lean), [GaussianOrderCombinations.lean](CircularLaw/GaussianOrderCombinations.lean) | Ordered norms are Lipschitz with constant one, so their sublevel events are closed and measurable. A union over deleted sets gives the actual binomial small-ball bound. For `m>=512`, the event at rank `floor(m/512)` and threshold `m/(512*n)` has probability at most `exp(-m/512)`. Fixed unit combinations have the same event law; finite unit sets cost their cardinality | Non-flatness content of LLTTY21 Lemma 4.3 and finite-set input to Proposition 4.4 |
| [ComplexSphereGrid.lean](CircularLaw/ComplexSphereGrid.lean), [GaussianNonflatNet.lean](CircularLaw/GaussianNonflatNet.lean), [GaussianNonflatUniform.lean](CircularLaw/GaussianNonflatUniform.lean) | Actual canonical grid, normalization and cardinality bound; compact projection proves measurability for some unit coefficient. At sufficiently large n, `m>=sqrt(n)` and `p<=n^(1/4)` give failure at most `exp(-m/2048)` for some unit combination to have rank `floor(m/2048)` at most `m/(2048*n)`. The complementary measurable event makes every unit combination nonzero | Uniform non-flatness content of LLTTY21 Proposition 4.4, with explicit constants and floor ranks |
| [GaussianForbiddenComparisons.lean](CircularLaw/GaussianForbiddenComparisons.lean), [GaussianSourceRange.lean](CircularLaw/GaussianSourceRange.lean) | The full standing range gives `L>=sqrt(n)`, `p<=n^(1/4)`, `log(n)<=n/L`, and the exact small positive floor rank. The largest-coordinate estimate implies every reverse-steepness inequality, and exponent 8192 absorbs the combination radius | Uniform parameter and forbidden-vector comparisons |
| [GaussianExceptionalContradiction.lean](CircularLaw/GaussianExceptionalContradiction.lean), [GaussianAntiClusteringTheorem.lean](CircularLaw/GaussianAntiClusteringTheorem.lean) | Three success events have a common sample; an oversized actual exceptional set contradicts the exact structural alternatives. The full named conclusion holds with admissible normal constant `1/2048` and common radius/failure constant 9216 | `prop:Gaussian-anti-clustering` proved in the standing manuscript context |
| [GaussianRowSpanExtension.lean](CircularLaw/GaussianRowSpanExtension.lean) | Literal least-coordinate projection, normalization and iteration give prescribed rank and containment, including rank deficiency. Retained-row locality, finite-sample measurability and joint Gaussian-normal measurability are checked. Structural alternatives transfer to the enlargement, projection norms decrease, and the structural theorem permits every fixed positive normal parameter at most one | Measurable enlargement and parameter compatibility for the random-normal and intermediate-singular-value arguments; input to the proved full intermediate theorem |
| [FiniteDiskConcentration.lean](CircularLaw/FiniteDiskConcentration.lean) | The finite-law concentration supremum over all closed complex disks is attained, bounded and measurable for continuous values | Actual supremum inside the expectation in Section 6 |
| [GaussianFreshRowParameters.lean](CircularLaw/GaussianFreshRowParameters.lean) | Both source codimensions lie in the full Gaussian range; exceptional fractions, occupancy tails and Gaussian radii have uniform lower-band bounds | Parameter comparisons for Sections 6–7 |
| [GaussianFreshRowSmallBall.lean](CircularLaw/GaussianFreshRowSmallBall.lean) | Full averaged concentration bound for the actual projected Gaussian normal, with structural and Gaussian failures charged separately | Section 6, `eq:averaged-normal-small-ball` |
| [FreshRowGaussianProbability.lean](CircularLaw/FreshRowGaussianProbability.lean) | Exact finite omitted-row resampling, retained-span invariance and integral Fubini yield the actual shifted row small-ball bound on the matrix–Gaussian product law | Section 7, `eq:row-normal-small-ball` |
| [GaussianRowDistance.lean](CircularLaw/GaussianRowDistance.lean) | Projection norm equals metric distance; small distance gives Gaussian small-ball probability at least one half; the full uniform per-index row-distance bound follows | Section 7, `eq:Gaussian-distance-implication` and `eq:leave-one-out-distance-prob`; input to the proved full intermediate singular-value theorem |
| [BadRowMarkov.lean](CircularLaw/BadRowMarkov.lean) | Exact bad-row expectation is the sum of per-index probabilities; Markov at the source ceiling threshold gives `R/d+R*d^2/n` and the uniform bound `2*R/d` | Section 7, `eq:bad-row-Markov`, without independence of distance events |
| [RowDeletion.lean](CircularLaw/RowDeletion.lean) | Select exactly `N-t` surviving rows, preserve actual comparison distances and prove linear independence and full row rank; the closed uniform survival probability is at least `1-2*R/d` | Actual post-deletion matrix in Section 7 |
| [RowDistanceDual.lean](CircularLaw/RowDistanceDual.lean) | Geometric row duals lie in the retained span, are biorthogonal to the actual conjugated rows and have squared norm `D_i^-2`; distance and dual energy sums are bounded by `k/r^2` | Geometric part of the negative second-moment identity |
| [RowGramInverse.lean](CircularLaw/RowGramInverse.lean) | Exact reconstruction on the retained span proves the inverse row Gram matrix equals the dual Gram matrix; its diagonal and real trace equal inverse squared actual row distances | Inverse Gram step of the negative second-moment identity |
| [HermitianInverseTrace.lean](CircularLaw/HermitianInverseTrace.lean) | Unitary diagonalization and an explicit diagonal right inverse prove the inverse trace is the sum of inverse eigenvalues | Checked spectral dependency for the negative second moment |
| [RowNegativeSecondMoment.lean](CircularLaw/RowNegativeSecondMoment.lean) | Actual row Gram equals `H H*`; ordered nonnegative eigenvalue square roots are the retained matrix's singular values. The full-row-rank negative second-moment identity, post-deletion sum bound and closed uniform survival probability are checked | Section 2, `eq:negative-second-moment`, for the actual retained shifted matrix; Section 7, `eq:NSM-H`; input to the proved full intermediate theorem |
| [SingularValueCounting.lean](CircularLaw/SingularValueCounting.lean) | A decreasing positive list's inverse-square tail controls its first value; actual surviving singular values obey the square-root and `r/d` lower bounds | Section 7, `eq:intermediate-H`; source rounded index conditions are discharged below |
| [SpectralRayleighBounds.lean](CircularLaw/SpectralRayleighBounds.lean), [SpectralSubspaceComparison.lean](CircularLaw/SpectralSubspaceComparison.lean) | Spectral-coordinate energy, head/tail Rayleigh bounds, rank-nullity and subspace intersection prove ordered eigenvalue comparison through a linear isometry | Checked dimension argument for principal eigenvalue comparison |
| [EuclideanCoordinateEmbedding.lean](CircularLaw/EuclideanCoordinateEmbedding.lean), [PrincipalEigenvalueComparison.lean](CircularLaw/PrincipalEigenvalueComparison.lean), [RowSingularValueComparison.lean](CircularLaw/RowSingularValueComparison.lean) | Coordinate injection extends to an isometry preserving the principal quadratic form; actual retained row Grams are principal submatrices, so adding rows increases singular values at the same position | Section 7 comparison `s_j(A_z)>=s_j(H)`; no row-rank assumption is required |
| [IntermediateIndexBounds.lean](CircularLaw/IntermediateIndexBounds.lean) | Literal `m=floor(n/d^3)-1`, `t=ceil(n/d^2)` and `q0=m+2*t`; `q0<=5*n/d^2<n`; the zero-based index is `n-q0-1` and its surviving tail has exactly `t+1` terms | Section 7, `eq:q0-scale` and the index in `eq:intermediate-H` |
| [SquareSliceSingularValues.lean](CircularLaw/SquareSliceSingularValues.lean) | Singular values of the literal square shifted matrix are the ordered square roots of nonnegative `A A*` eigenvalues; actual retained row Gram is its principal submatrix | Full-matrix spectral identification in `thm:intermediate` |
| [IntermediateExponentialRadius.lean](CircularLaw/IntermediateExponentialRadius.lean), [IntermediateSingularValueTheorem.lean](CircularLaw/IntermediateSingularValueTheorem.lean), [FixedShiftIntermediateTheorem.lean](CircularLaw/FixedShiftIntermediateTheorem.lean) | Uniform source parameters and exponential absorption give the full finite-dimensional `B/d` failure bound; every fixed shift and lower-band sequence has success probability tending to one | `thm:intermediate` and its introductory restatement `thm:intro-intermediate`, both proved |
| [IntermediateDeletionBudget.lean](CircularLaw/IntermediateDeletionBudget.lean) | Exact deletion logarithmic cost is at most `5*log(d)/d` and tends to zero along every lower-band degree sequence | Section 7's finer `q0` scale and Section 9's deletion-count logarithmic-tail budget |
| [PositiveContractionGeometry.lean](CircularLaw/PositiveContractionGeometry.lean), [RegularizedDistanceGeometry.lean](CircularLaw/RegularizedDistanceGeometry.lean) | Literal positive-contraction quadratic form, `P^2<=P`, trace comparison, square-root norm identity, and convex one-Lipschitz regularized distance | Section 8 geometry inputs; no contraction or convexity premise remains assumed |
| [BernoulliCubeLaw.lean](CircularLaw/BernoulliCubeLaw.lean), [BernoulliQuadraticMoment.lean](CircularLaw/BernoulliQuadraticMoment.lean), [RegularizedDistanceMean.lean](CircularLaw/RegularizedDistanceMean.lean) | Actual independent Bernoulli law including endpoints, exact centered moments and covariance, exact `E f^2=D^2`, `mu<=D`, and the deterministic upper bound on every zero-one row | Section 8, `eq:DP` and the upper mean bound; deterministic upper bound used by the hybrid |
| [BernoulliLinearVariance.lean](CircularLaw/BernoulliLinearVariance.lean), [BernoulliMonomialOrthogonality.lean](CircularLaw/BernoulliMonomialOrthogonality.lean), [BernoulliQuadraticVariance.lean](CircularLaw/BernoulliQuadraticVariance.lean) | Actual Hermitian linear variance; centered-square and off-diagonal monomial orthogonality; exact quadratic variance formula and its bound by `p(1-p)*tr(P^2)` | Section 8, `eq:QP-variance` and `eq:LP-variance` |
| [RegularizedDistanceFourthMoment.lean](CircularLaw/RegularizedDistanceFourthMoment.lean), [RegularizedDistanceMeanComparison.lean](CircularLaw/RegularizedDistanceMeanComparison.lean) | Exact source squared-distance fluctuation, `Var(f^2)<=8*D^2`, `E f^4<=9*D^4` for `D>=1`, and full two-sided mean comparison `D/8<=mu<=D` | Moment and mean conclusions of the complete `lem:regularized-distance` |
| [BernoulliSliceFibers.lean](CircularLaw/BernoulliSliceFibers.lean), [BernoulliSliceConditioning.lean](CircularLaw/BernoulliSliceConditioning.lean) | Exact support-size fiber, cardinality and literal row vector; conditional events and full conditional measure equal the actual uniform row-slice law | Section 8, Bernoulli-to-slice conditioning correspondence |
| [BinomialStirlingMass.lean](CircularLaw/BinomialStirlingMass.lean), [BernoulliSliceMassBound.lean](CircularLaw/BernoulliSliceMassBound.lean) | Effective factorial estimates prove conditioning mass at least `1/(4*exp(1)^2*sqrt(d))` for every `1<=d<=n`, including the full-support endpoint | Section 8, conditioning mass lower bound |
| [BernoulliSliceTransfer.lean](CircularLaw/BernoulliSliceTransfer.lean) | Arbitrary events under the actual row-slice law transfer with factor `4*exp(1)^2*sqrt(d)`; literal Euclidean rows, norm bound and conditional regularized-distance tail corollary | Section 8, slice tails once Bernoulli concentration is proved |
| [TalagrandSliceOptimization.lean](CircularLaw/TalagrandSliceOptimization.lean) | Explicit scalar interpolation with `c=1/64`, one-coordinate exponential-moment estimate and final probability absorption | Scalar inputs to the complete `lem:convex-concentration` |
| [TalagrandGeometry.lean](CircularLaw/TalagrandGeometry.lean), [TalagrandFunctionSeparation.lean](CircularLaw/TalagrandFunctionSeparation.lean), [TalagrandMaskTransport.lean](CircularLaw/TalagrandMaskTransport.lean) | Compact disagreement-mask hull for arbitrary alphabets, attained convex distance, actual convex witness within `2*K*distance`, convex Lipschitz sublevel separation and distance decrease under coordinate maps | Geometric bridge in `lem:convex-concentration` |
| [TalagrandInductionGeometry.lean](CircularLaw/TalagrandInductionGeometry.lean) | Actual slice/projection witness lifting, squared-norm convexity and full squared-distance interpolation recursion | Geometric dimension-induction step |
| [TalagrandFiniteProduct.lean](CircularLaw/TalagrandFiniteProduct.lean), [TalagrandHolder.lean](CircularLaw/TalagrandHolder.lean), [TalagrandFiniteMoment.lean](CircularLaw/TalagrandFiniteMoment.lean) | Literal arbitrary coordinate probabilities, exact finite product disintegration, endpoint-valid weighted Holder and full induction prove `E exp(d_c^2/64)<=1/P(A)` | Complete finite product Talagrand moment theorem, including zero-mass slices |
| [TalagrandFiniteConcentration.lean](CircularLaw/TalagrandFiniteConcentration.lean), [TalagrandFiniteMeasure.lean](CircularLaw/TalagrandFiniteMeasure.lean), [TalagrandFiniteIndependence.lean](CircularLaw/TalagrandFiniteIndependence.lean) | Two-event separation bound and median tail `4*exp(-t^2/256)` for arbitrary finite product laws, actual product measures and finite-valued independent variables on arbitrary probability spaces | Finite-law median conclusion; no concentration input or product-law correspondence assumed |
| [ComplexFiniteApproximation.lean](CircularLaw/ComplexFiniteApproximation.lean) | Common finite complex disk alphabets, measurable labels, preservation of independence and almost-sure Euclidean convergence | Extension of the finite concentration theorem to arbitrary bounded independent complex laws |
| [ConcentrationLimit.lean](CircularLaw/ConcentrationLimit.lean), [GaussianTwoEventLimit.lean](CircularLaw/GaussianTwoEventLimit.lean), [ConvexProductMedian.lean](CircularLaw/ConvexProductMedian.lean) | Product-space Fatou passes two-event bounds to limits; positive slack handles atoms at closed thresholds; full general median tail `4*exp(-t^2/256)` | Median-centered conclusion of `lem:convex-concentration` |
| [GaussianMedianMean.lean](CircularLaw/GaussianMedianMean.lean), [ConvexProductConcentrationProof.lean](CircularLaw/ConvexProductConcentrationProof.lean) | Layer-cake proves integrability and `E|F-m|<=64*K`; complete median- and mean-centered theorem with common constants `c=1/1024`, `C=4*exp(16)` | Full `lem:convex-concentration`; target `ConvexProductConcentrationLemma` |
| [FiniteLawMedian.lean](CircularLaw/FiniteLawMedian.lean), [RegularizedDistanceConcentration.lean](CircularLaw/RegularizedDistanceConcentration.lean) | A median for every finite probability law; actual Bernoulli mean tail and full slice tail with `sqrt(d)` loss, together with `D/8<=mu<=D` for `D>=1` | Full `lem:regularized-distance`; no concentration or conditioning input remains assumed |
| [TruncatedGaussianMoment.lean](CircularLaw/TruncatedGaussianMoment.lean), [DistanceLogDegreeMoment.lean](CircularLaw/DistanceLogDegreeMoment.lean) | A Gaussian cutoff absorbs the prefactor; layer-cake bounds the actual slice and Bernoulli absolute first moments by `288*sqrt(log(e*d))` | Tail integration in `lem:one-row-log` |
| [LogComparisonGeometry.lean](CircularLaw/LogComparisonGeometry.lean), [LogComparisonExpectation.lean](CircularLaw/LogComparisonExpectation.lean) | Pointwise logarithmic bounds above half the mean and within `[eta,U]`; integrates the good/bad comparison for arbitrary joint laws | Good-event and exceptional-event arguments in `lem:one-row-log` |
| [OneRowLogRates.lean](CircularLaw/OneRowLogRates.lean), [OneRowLogScale.lean](CircularLaw/OneRowLogScale.lean) | Actual trace gives `D>=sqrt(Q)` and `mu>=sqrt(Q)/8`; full `sqrt(log(e*d)/Q)` good rate and `exp(-Q/262144)` exceptional rate | Scalar and codimension inputs to `lem:one-row-log` |
| [FiniteLawTransport.lean](CircularLaw/FiniteLawTransport.lean), [OneRowLogComparison.lean](CircularLaw/OneRowLogComparison.lean) | Exact marginal laws transport integrals, integrability and tails; the full one-row logarithmic estimate holds on arbitrary probability spaces for every coupling and an almost-sure upper bound | Full `lem:one-row-log`; target `OneRowLogComparisonLemma` |
| [HybridRidgeGram.lean](CircularLaw/HybridRidgeGram.lean), [HybridComparisonMatrix.lean](CircularLaw/HybridComparisonMatrix.lean), [HybridComparisonTrace.lean](CircularLaw/HybridComparisonTrace.lean) | Actual ridge Gram positivity and inverse identity; comparison and conjugate matrices are positive contractions; the original fixes the kernel; exact trace identity gives `n-k+1` | Matrix inputs to `prop:row-replacement` |
| [HybridSchurDeterminant.lean](CircularLaw/HybridSchurDeterminant.lean), [HybridLogPotential.lean](CircularLaw/HybridLogPotential.lean), [HybridOneRowIncrement.lean](CircularLaw/HybridOneRowIncrement.lean), [HybridRowReindex.lean](CircularLaw/HybridRowReindex.lean) | Literal inserted-row determinant factorization with the required complex conjugation; exact logarithmic potential increment; uniform expected increment with other rows fixed; arbitrary row isolation preserves the potential | Schur and single-increment arguments in Section 8 |
| [FiniteProductConditioning.lean](CircularLaw/FiniteProductConditioning.lean), [IndependentFiniteFamilies.lean](CircularLaw/IndependentFiniteFamilies.lean), [RowHybrid.lean](CircularLaw/RowHybrid.lean), [RowHybridExpectation.lean](CircularLaw/RowHybridExpectation.lean) | Actual prefix hybrids and attained maximum shift norm; finite product conditioning, exact pair marginal laws, and the full conditional expected increment; the source independence assumptions give the actual product law of row pairs | Conditioning step in `prop:row-replacement` |
| [RowReplacementTelescoping.lean](CircularLaw/RowReplacementTelescoping.lean), [RowReplacementTheorem.lean](CircularLaw/RowReplacementTheorem.lean) | Telescopes expected absolute increments without assuming their independence; `k/n<=1` preserves the one-row bound; exact law transport proves the full source proposition on arbitrary probability spaces with common constants `C=10000+2*rowDistanceTailConstant`, `c=1/262144` | Full `prop:row-replacement`; target `GeneralizedRowReplacementProposition` |
| [LogTruncationGeometry.lean](CircularLaw/LogTruncationGeometry.lean), [LogTruncationIntegrals.lean](CircularLaw/LogTruncationIntegrals.lean) | Continuous bounded positive and negative logarithmic truncations; positive excess bounded by the second moment divided by the threshold; dominated convergence at the source finite logarithmic limit | Analytic truncation inputs to `lem:negative-log-tail` |
| [VaryingProbabilityConvergence.lean](CircularLaw/VaryingProbabilityConvergence.lean), [EmpiricalLogGeometry.lean](CircularLaw/EmpiricalLogGeometry.lean), [EmpiricalWeakConvergence.lean](CircularLaw/EmpiricalWeakConvergence.lean), [EmpiricalPositiveLogConvergence.lean](CircularLaw/EmpiricalPositiveLogConvergence.lean), [EmpiricalNegativeLogConvergence.lean](CircularLaw/EmpiricalNegativeLogConvergence.lean) | Probability limits on arbitrary varying sample spaces; exact `1/n` empirical means; weak convergence plus tight second moments gives the positive-log limit; the full signed-log limit gives the negative-log limit and vanishing zero-event probability | All three source hypotheses retained in the log-tail argument |
| [EmpiricalNegativeLogUI.lean](CircularLaw/EmpiricalNegativeLogUI.lean), [BottomLogGeometry.lean](CircularLaw/BottomLogGeometry.lean), [BottomLogConvergence.lean](CircularLaw/BottomLogConvergence.lean) | Literal iterated limsup conclusion; exact bottom-index count and threshold bound; `r/n->0` gives the bottom-log probability limit | Both conclusions of `lem:negative-log-tail` |
| [NonnegativeEmpiricalMeasure.lean](CircularLaw/NonnegativeEmpiricalMeasure.lean), [ExtendedEmpiricalLog.lean](CircularLaw/ExtendedEmpiricalLog.lean), [NegativeLogUniformIntegrability.lean](CircularLaw/NegativeLogUniformIntegrability.lean) | Actual empirical probability measure, real and Lebesgue integral identities, infinity at zero and exact finite-limit event encodings; full named lemma with both extended-valued conclusions and every source hypothesis | Full `lem:negative-log-tail`; target `NegativeLogUniformIntegrabilityLemma` |
| [SquareSingularSecondMoment.lean](CircularLaw/SquareSingularSecondMoment.lean), [MatrixEnergyShift.lean](CircularLaw/MatrixEnergyShift.lean), [BernoulliSquareMatrixLaw.lean](CircularLaw/BernoulliSquareMatrixLaw.lean), [BernoulliSecondMoment.lean](CircularLaw/BernoulliSecondMoment.lean) | Actual independent-entry Bernoulli matrix and `p=d/n` law; exact expected entry count `n*d`; the singular-value second moment equals entrywise energy divided by `n`; expectation at most `2+2*abs(z)^2` and Markov give tightness | Full part (iii) of `prop:Bernoulli-hermitization`; parts (i) and (ii) are proved below |
| [BernoulliLogTailReduction.lean](CircularLaw/BernoulliLogTailReduction.lean) | Measurable decreasing actual singular-value array and checked tight second moment supply the negative-log UI and bottom-tail deductions, with weak and full-log convergence left as explicit hypotheses | Conditional reduction for `cor:Bernoulli-bottom-tail`; its convergence inputs and full corollary are proved below |
| [MonotonePrefixMean.lean](CircularLaw/MonotonePrefixMean.lean), [SquareLogPrefixComparison.lean](CircularLaw/SquareLogPrefixComparison.lean) | Exact lower comparison `U >= (n/ell)*T1` for every positive integer prefix length at most `n`, on samples with positive singular values; negative logarithms need no sign restriction | Deterministic finite branch of `eq:SSS-U-lower-exact`; the probabilistic squeeze remains open |
| [SmallValueLogIntegrability.lean](CircularLaw/SmallValueLogIntegrability.lean) | Linear small-value mass bound gives zero mass at zero, an integrable negative logarithm with integral at most `2*C`, and bounded support gives an integrable positive logarithm | Finiteness implication used after SSS25 Fact 10.1; actual Gaussian weak-law existence, support and linear mass bounds are proved below |
| [SpectralCodimensionComparison.lean](CircularLaw/SpectralCodimensionComparison.lean), [PrincipalEigenvalueInterlacing.lean](CircularLaw/PrincipalEigenvalueInterlacing.lean), [RectangularSingularInterlacing.lean](CircularLaw/RectangularSingularInterlacing.lean) | Leading-subspace intersections give exact isometry and kernel dimension losses; both sides of actual Hermitian principal interlacing; rectangular row deletion gives exact singular-value index loss | Checked spectral and row-deletion inputs for hermitization |
| [MatrixColumnRestriction.lean](CircularLaw/MatrixColumnRestriction.lean), [ColumnSingularInterlacing.lean](CircularLaw/ColumnSingularInterlacing.lean), [PrincipalSingularInterlacing.lean](CircularLaw/PrincipalSingularInterlacing.lean) | Actual erased-coordinate kernel, its codomain dimension and Gram quadratic equality; both column-deletion bounds; combined `2*(n-m)` shift for an actual square principal minor | Complete deterministic row and column interlacing application |
| [ExactMinorLogComparison.lean](CircularLaw/ExactMinorLogComparison.lean) | Compatible finite upper comparison with half-open ambient interval `[2*(n-m),m)`, exact cardinality and tail coefficient; explicit integer conditions and positivity only in the retained minor prefix | Checked finite correction proposal; corrected probabilistic squeeze and truncation and rounding limits remain open |
| [SmallValueCutoff.lean](CircularLaw/SmallValueCutoff.lean), [RetainedPrefixSmallValues.lean](CircularLaw/RetainedPrefixSmallValues.lean) | Continuous cutoff, exact ordered-tail count and mass-bound integral estimate; a prefix omitting fraction `eta` has no value below `eta/(4*C)` with probability tending to one | Retained-prefix lower-bound deduction from weak convergence and the limiting linear small-value mass bound; discarded zeros are permitted |
| [BernoulliSqueezeRounding.lean](CircularLaw/BernoulliSqueezeRounding.lean) | Both literal floors; removed prefix fraction at least `epsilon`; `m/n`, `ell/n` and `n/ell` tend to one; vanishing removed fractions, compatible base count and eventual deleted-shift bound | Integer conditions for the corrected finite comparison; no random-matrix input assumed |
| [VaryingProbabilityTransfer.lean](CircularLaw/VaryingProbabilityTransfer.lean), [EmpiricalPrefixMeans.lean](CircularLaw/EmpiricalPrefixMeans.lean) | Uniform vanishing errors and vanishing probability tolerances transfer limits; actual prefix sum divided by `n`; exact omitted-fraction error for bounded tests; fixed clipped-log convergence and equality to the untruncated negative prefix on the no-small event | Checked bounded-test and fixed-cutoff foundation for the full `T1` deduction below |
| [BernoulliPrefixConvergence.lean](CircularLaw/BernoulliPrefixConvergence.lean) | Applies the retained-value bound and negative-clipped prefix convergence to the actual Bernoulli law and source floors; identifies the literal square negative-log prefix | The Bernoulli weak input and Gaussian mass bound are proved below; full interface is proved below using the actual greedy estimate |
| [SlowDiagonal.lean](CircularLaw/SlowDiagonal.lean), [LogarithmicStages.lean](CircularLaw/LogarithmicStages.lean), [SqueezeRoundingError.lean](CircularLaw/SqueezeRoundingError.lean) | Monotone stage choice tending to infinity, integer cutoffs and positive decreasing fractions; vanishing fraction times cutoff; exact omitted source fraction at most `5*epsilon/4+2/n` | Explicit slow choice for the retained-prefix convergence argument |
| [PrefixNegativeDeviation.lean](CircularLaw/PrefixNegativeDeviation.lean), [RoundedNegativePrefixConvergence.lean](CircularLaw/RoundedNegativePrefixConvergence.lean) | Joint control of the small-value event, full clipped-mean deviation and rounding error; full untruncated negative-prefix limit and vanishing retained-zero probability | Uses weak convergence, limiting small-value mass and finite logarithmic integral; assumes no empirical full-log convergence |
| [EmpiricalPositivePrefixConvergence.lean](CircularLaw/EmpiricalPositivePrefixConvergence.lean), [RoundedLogPrefixConvergence.lean](CircularLaw/RoundedLogPrefixConvergence.lean) | Tight second moments make the omitted positive logarithms vanish; both logarithmic parts converge along the same checked slow selector | Complete signed-prefix potential deduction |
| [BernoulliSlowPrefixLimit.lean](CircularLaw/BernoulliSlowPrefixLimit.lean) | Actual Bernoulli law and literal two-floor `T1`; positive nonincreasing `epsilon_n->0`; full prefix potential tends to `-integral(log,nu)` and retained zeros have vanishing probability | Closed T1 deduction; Gaussian inputs and common literal minor T convergence are proved below; the full upper estimate is proved below; the reviewed rounding comparison remains open |
| [SlowProbabilityLimits.lean](CircularLaw/SlowProbabilityLimits.lean), [BernoulliJointPrefixLimit.lean](CircularLaw/BernoulliJointPrefixLimit.lean) | The `T1` selector preserves additional eventual constraints; auxiliary fixed-fraction limits converge along the same selector | Common slow-choice deduction; the auxiliary limits are explicit inputs |
| [VaryingProbabilitySqueeze.lean](CircularLaw/VaryingProbabilitySqueeze.lean), [BernoulliLogSqueeze.lean](CircularLaw/BernoulliLogSqueeze.lean), [BernoulliSlowLogSqueeze.lean](CircularLaw/BernoulliSlowLogSqueeze.lean) | Deterministic normalization transfer, squeeze with explicit singular events, and one slow choice deriving the actual full extended-log limit from fixed-fraction minor limits and upper estimates | Complete conditional assembly; Gaussian/circular identification is proved below; the common literal minor-prefix limit is proved below; upper estimates are supplied by the actual greedy process below |
| [SquareSingularDeterminant.lean](CircularLaw/SquareSingularDeterminant.lean), [BernoulliLogDeterminant.lean](CircularLaw/BernoulliLogDeterminant.lean) | Actual singular-value product equals absolute determinant; zero-event equivalence; full log convergence transfers to the normalized log determinant, with vanishing singular probability | Algebraic determinant bridge is unconditional; convergence deduction uses the full Bernoulli log limit proved below |
| [UnitaryMatrixEnergy.lean](CircularLaw/UnitaryMatrixEnergy.lean), [UnitaryEigenvectorReduction.lean](CircularLaw/UnitaryEigenvectorReduction.lean), [SchurBlockReduction.lean](CircularLaw/SchurBlockReduction.lean), [SchurEigenvalueEnergy.lean](CircularLaw/SchurEigenvalueEnergy.lean) | Actual unitary first-eigenvector reduction, characteristic-polynomial factorization, energy budget and dimension induction | Full Schur eigenvalue energy bound for every complex matrix, retaining algebraic multiplicities |
| [CharacteristicRootScaling.lean](CircularLaw/CharacteristicRootScaling.lean), [EmpiricalSpectralIntegrals.lean](CircularLaw/EmpiricalSpectralIntegrals.lean), [EigenvalueFirstMoment.lean](CircularLaw/EigenvalueFirstMoment.lean) | Exact root scaling including scalar zero, literal finite Dirac integrals and Cauchy-Schwarz first-moment bound | Complete algebraic and integral inputs to ESD normalization transfer |
| [SpectralRescalingBound.lean](CircularLaw/SpectralRescalingBound.lean), [VarianceNormalizationTransfer.lean](CircularLaw/VarianceNormalizationTransfer.lean) | Full bounded-Lipschitz triangle and rescaling bounds; actual row-slice error at most `abs((1-d/n)^(-1/2)-1)`; uniform vanishing error and probability transfer under either regime filter | Complete variance-normalization transfer; degree-normalized circular-law estimates remain unproved |
| [CharacteristicRootShift.lean](CircularLaw/CharacteristicRootShift.lean), [SpectralLogPotential.lean](CircularLaw/SpectralLogPotential.lean), [SpectralLogConvergence.lean](CircularLaw/SpectralLogConvergence.lean) | Exact shifted roots, atoms and singular shifts; actual ESD potential equals the shifted log determinant almost everywhere and its extended singular logarithm everywhere | Full deterministic bridge; convergence transfer still requires actual full singular-log convergence |
| [PlanarLogIntegrability.lean](CircularLaw/PlanarLogIntegrability.lean), [PlanarSquaredLog.lean](CircularLaw/PlanarSquaredLog.lean), [SpectralLogSquareBound.lean](CircularLaw/SpectralLogSquareBound.lean) | Polar integration controls logarithmic singularities; local absolute and square integrability; disk L2 bound `32*pi + 2*area(disk)*(R^2+energy/n)` | Uniform row-slice and Bernoulli probability bounds supply the proved replacement principle |
| [SpectralEnergyTightness.lean](CircularLaw/SpectralEnergyTightness.lean) | Actual ESD second moment and radial tail are bounded by normalized matrix energy; uniform row-slice tightness and Bernoulli tightness in probability | Checked tightness input to the replacement principle |
| [SpatialSquareGeometry.lean](CircularLaw/SpatialSquareGeometry.lean), [SpatialBadArea.lean](CircularLaw/SpatialBadArea.lean), [SpatialProbabilityConvergence.lean](CircularLaw/SpatialProbabilityConvergence.lean) | Actual Fubini and dominated-convergence proofs on varying probability spaces; almost-everywhere pointwise convergence in probability and spatial L2 control imply spatial L1 and bounded-test integral convergence | Spatial probability passage of the replacement argument proved |
| [VaryingProbabilityBounded.lean](CircularLaw/VaryingProbabilityBounded.lean), [LogDeterminantSpatialConvergence.lean](CircularLaw/LogDeterminantSpatialConvergence.lean) | Canonical Borel matrix measurability; actual energy controls spatial squared log differences; pointwise log-determinant convergence implies spatial L1 convergence and whole-plane compact-test convergence of actual ESD potentials | Spatial passage of the replacement argument |
| [PlanarLogApproximateIdentity.lean](CircularLaw/PlanarLogApproximateIdentity.lean), [SmoothedPlanarLog.lean](CircularLaw/SmoothedPlanarLog.lean) | Actual planar positive kernel has mass one and approximates evaluation at zero; smoothed logarithm is smooth, with actual Fréchet derivatives and Laplacian `2*epsilon^2/(norm(z)^2+epsilon^2)^2` | Exact `2*pi` fundamental-solution normalization |
| [PlanarGreenIdentity.lean](CircularLaw/PlanarGreenIdentity.lean), [PlanarLogFundamentalSolution.lean](CircularLaw/PlanarLogFundamentalSolution.lean) | Full Green identity for every compact C2 test and arbitrary C2 weight; dominated convergence at the logarithmic singularity; exact identity `integral(log(norm(z-w))*Laplacian(phi)(z)) = 2*pi*phi(w)` | Distributional logarithmic-kernel identity proved at every point |
| [SpectralLogReconstruction.lean](CircularLaw/SpectralLogReconstruction.lean) | Algebraic multiplicities retained; actual ESD/log-determinant reconstruction and convergence of every compact C2 eigenvalue test integral from energy bounds and almost-everywhere log-difference convergence | Reconstruction step in the proved replacement principle |
| [BLCompactSmoothApproximation.lean](CircularLaw/BLCompactSmoothApproximation.lean), [BLFiniteApproximation.lean](CircularLaw/BLFiniteApproximation.lean), [BLFiniteSmoothFamily.lean](CircularLaw/BLFiniteSmoothFamily.lean) | Actual BL restrictions have compact closure by Arzela--Ascoli; finite centers retain global bound one; smoothing and disk cutoff give a finite compact C2 family, globally bounded by two, covering every BL test on the disk | Constructed finite family for the full BL supremum |
| [BLIntegralApproximation.lean](CircularLaw/BLIntegralApproximation.lean), [BLFiniteSpectralBound.lean](CircularLaw/BLFiniteSpectralBound.lean), [VaryingFiniteTestProbability.lean](CircularLaw/VaryingFiniteTestProbability.lean), [BLProbabilityConvergence.lean](CircularLaw/BLProbabilityConvergence.lean) | Integral error at most disk error plus three times outer mass; energy controls both tails; a finite probability union proves convergence of the full BL distance from compact C2 tests | Full bounded-Lipschitz extension proved on varying probability spaces |
| [ReplacementPrinciple.lean](CircularLaw/ReplacementPrinciple.lean), [ReplacementLimitTransfer.lean](CircularLaw/ReplacementLimitTransfer.lean) | Actual matrix energy and almost-everywhere log-determinant differences imply full BL convergence; combined energy and classical `1/sqrt(n)` normalization checked; transfers any actual comparator limit | Tao--Vu Theorem 2.1's probability version used by the paper proved; actual circular-law comparator limits and logarithmic comparisons remain obligations |
| [CircularPotentialPolar.lean](CircularLaw/CircularPotentialPolar.lean), [RadialCircularPotential.lean](CircularLaw/RadialCircularPotential.lean), [CircularLogPotential.lean](CircularLaw/CircularLogPotential.lean) | Actual unit-disk logarithmic integral, exact inside and outside formulas at every point, manuscript negative sign, continuity and spatial square bounds | Circular-measure side of the potential identity proved; identification with the actual Gaussian singular law is proved below |
| [CircularLogReconstruction.lean](CircularLaw/CircularLogReconstruction.lean) | Uniform compact-test section bounds prove joint integrability; Fubini and the actual fundamental solution reconstruct the circular measure with exact factor `2*pi` | Actual circular target reconstruction proved |
| [CircularSpatialConvergence.lean](CircularLaw/CircularSpatialConvergence.lean), [BLCircularConvergence.lean](CircularLaw/BLCircularConvergence.lean), [CircularHermitization.lean](CircularLaw/CircularHermitization.lean) | Actual energy control and almost-everywhere shifted-log-determinant convergence to the proved circular potential yield full BL circular convergence, including the paper negative sign | Direct hermitization criterion proved; actual matrix-model logarithmic limits remain obligations |
| [ComplexGaussianMoments.lean](CircularLaw/ComplexGaussianMoments.lean), [ComplexGaussianRotation.lean](CircularLaw/ComplexGaussianRotation.lean), [GaussianEntryProducts.lean](CircularLaw/GaussianEntryProducts.lean) | Actual complex Gaussian polynomial moments are integrable; mixed moments vanish unless powers match and otherwise equal the factorial; independent-entry words retain repeated-index multiplicities and have exact product-factorial expectations and factorial bounds | Gaussian trace-moment inputs proved; every shifted weak singular law is constructed below; its logarithmic identification is proved below |
| [GaussianWickFour.lean](CircularLaw/GaussianWickFour.lean), [GaussianCoordinateMoments.lean](CircularLaw/GaussianCoordinateMoments.lean), [GaussianLinearSecondMoment.lean](CircularLaw/GaussianLinearSecondMoment.lean) | Exact four-entry pairing identity includes coincident indices; Gaussian marginals, affine-coordinate energies, Kronecker covariance and every deterministic complex linear-form mean-square norm checked | Actual Gaussian entry and linear-form moment inputs proved |
| [GaussianSquareMatrixLaw.lean](CircularLaw/GaussianSquareMatrixLaw.lean), [GaussianGramTraceMoments.lean](CircularLaw/GaussianGramTraceMoments.lean), [SquareSingularTraceMoments.lean](CircularLaw/SquareSingularTraceMoments.lean) | Actual iid complex Gaussian matrix and shifted singular law; exact shifted second-moment mean `1+norm(z)^2`; `E trace((G G*)^2)=2*n^3`; every even empirical singular moment equals the actual Gram trace divided by dimension | Gaussian matrix trace inputs and deterministic trace-to-singular-moment identity proved |
| [GaussianSingularMoments.lean](CircularLaw/GaussianSingularMoments.lean), [GaussianProductEnergy.lean](CircularLaw/GaussianProductEnergy.lean), [GaussianEnergyConvergence.lean](CircularLaw/GaussianEnergyConvergence.lean) | Shifted second moments bounded in probability; zero-shift normalized fourth-moment mean exactly two; normalized energy centered square mean `1/n^2`; deviation probability at most `1/(n^2*epsilon^2)` proves zero-shift second-moment convergence to one | Low-order Gaussian model calculations checked; all-order shifted moment concentration and weak convergence are proved below; logarithmic identification is proved below |
| [MatrixEnergyShiftIdentity.lean](CircularLaw/MatrixEnergyShiftIdentity.lean), [GaussianShiftedSecondMoment.lean](CircularLaw/GaussianShiftedSecondMoment.lean) | Exact energy shift identity retains the trace cross term; Gaussian correction square mean at most `4*norm(z)^2/n^2` and deviation bound at most `4*norm(z)^2/(n^2*epsilon^2)`; every fixed-shift singular second moment converges to `1+norm(z)^2` in probability | Actual shifted second moment converges; full weak convergence and identification of the limiting second moment are proved below |
| [GaussianPolynomialMoments.lean](CircularLaw/GaussianPolynomialMoments.lean), [GaussianPolynomialSquareMoments.lean](CircularLaw/GaussianPolynomialSquareMoments.lean), [GaussianTracePolynomials.lean](CircularLaw/GaussianTracePolynomials.lean) | Arbitrary entry polynomials have exact support-sum expectations and integrable norm powers; coefficient conjugation and variable exchange evaluate to actual conjugation; every shifted Gram trace and centered square expectation has an exact finite formula; every even shifted singular moment is integrable with that normalized mean | All-order finite matrix moment calculations checked; all shifted moment limits and concentration are proved below |
| [GaussianPolynomialImbalance.lean](CircularLaw/GaussianPolynomialImbalance.lean), [GaussianMatrixWords.lean](CircularLaw/GaussianMatrixWords.lean), [GaussianScaledMatrixWords.lean](CircularLaw/GaussianScaledMatrixWords.lean) | Weighted homogeneous polynomials at nonzero direct/conjugate imbalance have zero expectation; arbitrary noncommuting matrix words evaluate to actual products; unequal direct/adjoint counts give zero trace expectation, including every complex scalar normalization | All-order unbalanced-word cancellation proved; limiting balanced contributions and covariance limits are proved below |
| [MatrixGramShiftTrace.lean](CircularLaw/MatrixGramShiftTrace.lean), [GaussianScaledGramMoments.lean](CircularLaw/GaussianScaledGramMoments.lean), [GaussianShiftedFourthMoment.lean](CircularLaw/GaussianShiftedFourthMoment.lean) | Exact deterministic shifted Gram-square expansion uses trace cyclicity; Gaussian balanced means and all six unbalanced cancellations give shifted fourth singular-moment mean `2+4*norm(z)^2+norm(z)^4` at every positive dimension | Actual shifted fourth-moment expectation proved; convergence in probability and the limiting fourth moment are proved below |
| [GaussianPairingCount.lean](CircularLaw/GaussianPairingCount.lean), [GaussianWickPairings.lean](CircularLaw/GaussianWickPairings.lean) | Matching permutations are a torsor for label-preserving permutations; their number equals the product of entry multiplicity factorials; Wick's formula is a sum over every matching permutation at arbitrary order, with repeated indices retained and factorial norm bound | Full finite complex Gaussian Wick formula checked |
| [MatrixGramWalks.lean](CircularLaw/MatrixGramWalks.lean), [GaussianGramTracePairings.lean](CircularLaw/GaussianGramTracePairings.lean), [PermutationCycleColorings.lean](CircularLaw/PermutationCycleColorings.lean), [GaussianPairingCycleCounts.lean](CircularLaw/GaussianPairingCycleCounts.lean) | Every Gram power is an exact sum over closed row/column walks; Gaussian expectations pair all edges; cycle-invariant assignments have exactly `n^c` choices; Gram mean at power `k+1` equals the sum of `n^(cycles(sigma)+cycles(rotate*sigma^-1))`, and the normalized singular moment divides this sum by `n^(k+2)` | All-order exact zero-shift cycle-count formula proved; its asymptotic mean and concentration are checked below; Catalan enumeration is proved below |
| [FiniteIncidenceGraph.lean](CircularLaw/FiniteIncidenceGraph.lean), [PermutationCycleGraph.lean](CircularLaw/PermutationCycleGraph.lean), [GaussianMomentCycleBound.lean](CircularLaw/GaussianMomentCycleBound.lean) | Actual matching-cycle incidence graph is connected because the product is the cyclic successor; vertex and edge counts imply the exponent bound `cycles(sigma)+cycles(rotate*sigma^-1)<=k+2` | Dimension bound for every Gaussian Gram pairing, including fixed points and repeated indices |
| [DimensionPowerLimit.lean](CircularLaw/DimensionPowerLimit.lean), [GaussianMomentMeanLimits.lean](CircularLaw/GaussianMomentMeanLimits.lean) | Every normalized mean at order `2*(k+1)` is between zero and `(k+1)!` for positive dimension and tends to the exact count of permutations attaining exponent `k+2` | Actual all-order zero-shift mean limits; identification of these counts with Catalan numbers is proved below |
| [GaussianTwoTraceCycleBound.lean](CircularLaw/GaussianTwoTraceCycleBound.lean), [GaussianMixedPairingDecay.lean](CircularLaw/GaussianMixedPairingDecay.lean) | A matching crossing the two trace blocks makes the cycle incidence graph connected; its exponent is at most `2*(k+1)+1`; the sum of normalized crossing contributions is at most `(2*(k+1))!/n` and tends to zero | Exact combinatorial decay input for the actual variance identity below |
| [GaussianFinitePairings.lean](CircularLaw/GaussianFinitePairings.lean), [MatrixGramTraceProducts.lean](CircularLaw/MatrixGramTraceProducts.lean), [GaussianTwoTracePairings.lean](CircularLaw/GaussianTwoTracePairings.lean) | Wick matching on arbitrary finite position types; actual squared Gram trace expands into two closed walks and has second moment equal to the full two-block cycle sum | Every crossing and separate pairing retained in the actual second-moment calculation |
| [BlockPreservingPermutations.lean](CircularLaw/BlockPreservingPermutations.lean), [GaussianSeparatePairings.lean](CircularLaw/GaussianSeparatePairings.lean), [GaussianMomentVariance.lean](CircularLaw/GaussianMomentVariance.lean) | Block-preserving permutations are exactly two independent permutations; binary invariant-coloring counts prove cycle additivity; their sum is the squared mean; the actual centered square expectation is exactly the crossing sum and at most `(2*(k+1))!/n` | All-order zero-shift Gaussian singular-moment variance decay proved |
| [VaryingMeanSquareConvergence.lean](CircularLaw/VaryingMeanSquareConvergence.lean), [GaussianMomentConvergence.lean](CircularLaw/GaussianMomentConvergence.lean) | Markov gives deviation probability at most the centered square integral divided by `epsilon^2`; every positive even zero-shift moment converges in mean square and probability to its leading count; the fourth moment has the explicit limit two | Actual all-order zero-shift convergence proved; full shifted moment concentration and weak law are proved below; Catalan enumeration is proved below; logarithmic identification is proved below |
| [GaussianLeadingTrees.lean](CircularLaw/GaussianLeadingTrees.lean) | A pairing attains the maximal exponent exactly when its cycle incidence graph is a tree and the actual position-to-edge map is bijective | Checked characterization of the leading configurations; their Catalan enumeration is proved below |
| [ComplexLatticeNet.lean](CircularLaw/ComplexLatticeNet.lean), [ComplexHalfNetReduction.lean](CircularLaw/ComplexHalfNetReduction.lean) | Actual complex half-net has cardinality at most `exp(14*n)` and points of norm at most two; two-net inner-product control gives an operator bound with factor four | Constructed complex net and deterministic norm reduction |
| [GaussianLinearFormLaw.lean](CircularLaw/GaussianLinearFormLaw.lean), [GaussianLinearFormTails.lean](CircularLaw/GaussianLinearFormTails.lean), [GaussianMatrixBilinearTail.lean](CircularLaw/GaussianMatrixBilinearTail.lean) | Every finite linear form has the actual scaled complex Gaussian law, including zero scale; radial tails and exact bilinear coefficient energy give the net-pair tail `exp(-(r/4)^2)` | Gaussian distribution and probability inputs proved |
| [GaussianMatrixNorm.lean](CircularLaw/GaussianMatrixNorm.lean), [ComplexMatrixOperatorBounds.lean](CircularLaw/ComplexMatrixOperatorBounds.lean), [GaussianShiftedNormSupport.lean](CircularLaw/GaussianShiftedNormSupport.lean) | Actual matrix operator norm is at most `128*sqrt(n)` with failure probability at most `exp(-36*n)`; every normalized shifted singular value is at most `128+norm(z)` with the same bound | Finite-sample upper singular-value estimate proved |
| [VaryingProbabilityUnique.lean](CircularLaw/VaryingProbabilityUnique.lean), [GaussianWeakLimitSupport.lean](CircularLaw/GaussianWeakLimitSupport.lean) | Tests vanishing below `128+norm(z)` converge to zero; uniqueness and a positive continuous cutoff show any actual shifted weak limit has no mass above this radius | Support inheritance proved; general shifted weak-law existence and linear mass bounds are proved below |
| [VaryingProbabilityPolynomial.lean](CircularLaw/VaryingProbabilityPolynomial.lean), [VaryingMomentSamples.lean](CircularLaw/VaryingMomentSamples.lean) | Every polynomial empirical mean is an exact finite combination of moments; finite probability unions select bounded samples whose first `k+1` moments have error at most `1/(k+1)` | Polynomial probability limits and simultaneous good samples proved |
| [CompactMomentExistence.lean](CircularLaw/CompactMomentExistence.lean), [CompactMomentConvergence.lean](CircularLaw/CompactMomentConvergence.lean) | Compactness of probability measures on the actual interval constructs a measure with every prescribed moment; Weierstrass approximation proves all continuous-test limits from the actual moment limits and upper-bound failure event | Complete compact moment-to-weak-law construction checked |
| [GaussianSquaredMomentLimits.lean](CircularLaw/GaussianSquaredMomentLimits.lean), [GaussianZeroWeakLimit.lean](CircularLaw/GaussianZeroWeakLimit.lean) | All actual squared singular moments converge; the zeroth moment is one; the compact construction and square-root pushforward prove weak convergence in probability of the actual zero-shift Gaussian singular law, with all even limiting moments equal to the leading pairing counts and support in `[0,128]` | Actual zero-shift weak law proved; general shifted law is proved below; Catalan enumeration is proved below; logarithmic identification is proved below |
| [EmpiricalWeakLimitUnique.lean](CircularLaw/EmpiricalWeakLimitUnique.lean), [GaussianZeroLimitProperties.lean](CircularLaw/GaussianZeroLimitProperties.lean) | Bounded continuous test integrals and uniqueness of deterministic probability limits identify finite weak limiting measures; the constructed zero-shift law is unique, with second moment one and fourth moment two | Actual zero-shift limiting measure and low moments checked |
| [ComplexGaussianShiftLaplace.lean](CircularLaw/ComplexGaussianShiftLaplace.lean), [GaussianShiftNormLaplace.lean](CircularLaw/GaussianShiftNormLaplace.lean), [GaussianShiftProjectionNorm.lean](CircularLaw/GaussianShiftProjectionNorm.lean) | Completing the square gives exact shifted Gaussian negative-exponential integrals; a projection of rank `p>0` has small-ball probability at most `(exp(1)*u/p)^p`, uniformly in the deterministic shift | Squared projected norm at most `p/8` has probability at most `2^(-p)` |
| [FiniteSpanDistanceMeasurable.lean](CircularLaw/FiniteSpanDistanceMeasurable.lean), [GaussianShiftSpanDistance.lean](CircularLaw/GaussianShiftSpanDistance.lean), [GaussianIndependentSpanDistance.lean](CircularLaw/GaussianIndependentSpanDistance.lean) | Distance to continuously varying finite row spans is measurable even at rank changes; orthogonal projection and Fubini give the shifted Gaussian distance estimate after conditioning on the other rows | With fewer than `n` conditioned rows, squared distance at most `(n-card(rows))/8` has probability at most `2^(-(n-card(rows)))`; distance is almost surely positive |
| [GaussianProductCurry.lean](CircularLaw/GaussianProductCurry.lean) | Uncurrying a finite product of Gaussian row laws gives exactly the independent-entry Gaussian matrix law | Connects row exposure with the actual matrix law used by the singular-value calculations |
| [GaussianRowExposure.lean](CircularLaw/GaussianRowExposure.lean), [GaussianShiftFullRank.lean](CircularLaw/GaussianShiftFullRank.lean) | Any selected row splits from all others under the actual product law; a finite union controls every distance; positive leave-one-out distances imply full row rank | Every normalized shifted square Gaussian matrix has nonzero determinant and positive singular values almost surely |
| [GaussianConjugateLaw.lean](CircularLaw/GaussianConjugateLaw.lean), [GaussianRowRestriction.lean](CircularLaw/GaussianRowRestriction.lean) | Characteristic functions prove scalar conjugation invariance; finite product maps preserve conjugated rows and every injective selection of actual square-matrix rows | Exact law needed for conjugated row distances and row interlacing |
| [FiniteRowDistanceDual.lean](CircularLaw/FiniteRowDistanceDual.lean), [FiniteRowGramInverse.lean](CircularLaw/FiniteRowGramInverse.lean), [FiniteRowNegativeSecondMoment.lean](CircularLaw/FiniteRowNegativeSecondMoment.lean), [GaussianRectangularDistances.lean](CircularLaw/GaussianRectangularDistances.lean) | Geometric duals identify the inverse Gram trace with both inverse squared row distances and actual rectangular singular values; conjugated rows have Gram `A A*` | For `k` Gaussian rows in `n` columns, inverse moment at most `8*k/(n-k+1)` with failure at most `k*2^(-(n-k+1))`, uniformly in deterministic shifts |
| [ComplexRowDistanceScaling.lean](CircularLaw/ComplexRowDistanceScaling.lean), [GaussianIntermediateSingularBounds.lean](CircularLaw/GaussianIntermediateSingularBounds.lean), [GaussianSmallValueQuantiles.lean](CircularLaw/GaussianSmallValueQuantiles.lean) | Exact complex distance scaling, row interlacing and normalization control all retained positions; singular value at zero-based index `n-2*q` is at least `q/(4*n)` with failure at most `n*2^(-q)` when `0<q` and `2*q<n` | At `q=floor(eta*n)`, failure tends to zero and the quantile is eventually at least `eta/8` for `0<eta<1/3` |
| [OrderedSmallValueTests.lean](CircularLaw/OrderedSmallValueTests.lean), [VaryingProbabilityUpperBound.lean](CircularLaw/VaryingProbabilityUpperBound.lean), [GaussianWeakLimitSmallValues.lean](CircularLaw/GaussianWeakLimitSmallValues.lean) | Ordered continuous small-value tests are bounded by the tail fraction; deterministic probability limits inherit bounds outside vanishing bad events; a cutoff gives `nu([0,t))<=48*t` for all `t>0` | Linear small-value mass inheritance proved for every actual shifted Gaussian weak limit; construction at every shift is proved below |
| [GaussianWeakLimitLogIntegrability.lean](CircularLaw/GaussianWeakLimitLogIntegrability.lean) | Linear small-value mass gives zero atom at zero and integrable negative logarithm with integral at most 96; bounded support gives a finite full logarithmic integral | Finiteness is now unconditional for the constructed law at every shift, as proved below; identification with the circular potential is proved below |
| [FiniteRelationColorings.lean](CircularLaw/FiniteRelationColorings.lean), [FiniteLabeledGraph.lean](CircularLaw/FiniteLabeledGraph.lean), [PairedClosedWalk.lean](CircularLaw/PairedClosedWalk.lean) | Equality constraints give exactly `n^classes` vertex assignments; the quotient of a paired closed walk is connected and has at most `pairs+1` classes, including loops and repeated edges | Dimension exponent bound for arbitrary nonalternating words checked |
| [GaussianBijectionPairings.lean](CircularLaw/GaussianBijectionPairings.lean), [MatrixWordWalks.lean](CircularLaw/MatrixWordWalks.lean), [GaussianWordPairingCounts.lean](CircularLaw/GaussianWordPairingCounts.lean) | Direct and adjoint positions are matched by all actual bijections; exact ordered matrix-walk expansion and Wick integration give a sum of `n^vertexExponent` for every balanced word | Keeps every repeated-index and nonleading matching contribution |
| [GaussianWordMeanLimits.lean](CircularLaw/GaussianWordMeanLimits.lean), [GaussianNormalizedWordMeans.lean](CircularLaw/GaussianNormalizedWordMeans.lean), [GaussianAllWordMeans.lean](CircularLaw/GaussianAllWordMeans.lean) | Maximal-exponent counts give actual normalized complex trace-mean limits for every finite Gaussian word; unbalanced means vanish and the empty word has limit one | Full word-mean convergence checked; normalized word covariance limits are proved below |
| [MatrixScalarShiftWords.lean](CircularLaw/MatrixScalarShiftWords.lean), [FiniteListIntegralLimits.lean](CircularLaw/FiniteListIntegralLimits.lean), [GaussianShiftedMomentMeanLimits.lean](CircularLaw/GaussianShiftedMomentMeanLimits.lean) | Finite scalar-shift expansion retains order and multiplicity; integration and limits assemble every actual shifted Gram-trace and even singular-moment mean at every complex shift | Limiting means are real and nonnegative, with zeroth moment one; full shifted concentration and weak law are proved below; logarithmic identification is proved below |
| [PairedTwoClosedWalks.lean](CircularLaw/PairedTwoClosedWalks.lean), [GaussianTwoWordPairings.lean](CircularLaw/GaussianTwoWordPairings.lean) | Actual trace-product integrals pair the combined words; a cross pairing connects both quotient walks and loses a dimension power | Mixed pairing exponent at most total direct count plus one, for arbitrary positive word lengths |
| [SumBlockBijections.lean](CircularLaw/SumBlockBijections.lean), [PairedSumColorings.lean](CircularLaw/PairedSumColorings.lean), [GaussianSeparateWordPairings.lean](CircularLaw/GaussianSeparateWordPairings.lean) | Block-preserving matchings are exactly two separate bijections; coloring class counts add, so their integral sum factors into the product of single-word means | Exact separate-pairing cancellation, with empty matching types and unbalanced words included |
| [GaussianWordPairingBalance.lean](CircularLaw/GaussianWordPairingBalance.lean), [GaussianTwoWordCovariance.lean](CircularLaw/GaussianTwoWordCovariance.lean), [GaussianNormalizedWordCovariance.lean](CircularLaw/GaussianNormalizedWordCovariance.lean) | All-word finite integral formulas and actual square-root scaling identify normalized covariance with the mixed sum; its norm is at most total-direct-count factorial divided by n; empty-word covariance vanishes | Actual covariance tends to zero for every fixed finite pair of Gaussian words |
| [FiniteListSecondMoments.lean](CircularLaw/FiniteListSecondMoments.lean), [GaussianShiftedSecondMomentLimits.lean](CircularLaw/GaussianShiftedSecondMomentLimits.lean), [GaussianShiftedMomentConcentration.lean](CircularLaw/GaussianShiftedMomentConcentration.lean) | Every ordered term pair and its multiplicity is retained; shifted trace second means tend to the square of the first limit; Hermitian reality gives vanishing real centered-square means | Every actual even shifted Gaussian singular moment converges in mean square and probability |
| [GaussianShiftedSquaredMoments.lean](CircularLaw/GaussianShiftedSquaredMoments.lean), [GaussianShiftedWeakLimit.lean](CircularLaw/GaussianShiftedWeakLimit.lean), [GaussianShiftedLimitProperties.lean](CircularLaw/GaussianShiftedLimitProperties.lean) | Compact moments construct the unique actual weak limiting probability law at every complex shift; support below 128+norm(z), all even moment identities, second moment 1+norm(z)^2, fourth moment 2+4*norm(z)^2+norm(z)^4, linear small mass 48*t, zero atom and finite logarithmic integral | General shifted Gaussian weak law proved; circular logarithmic identification is proved below; sparse Bernoulli weak-law transfer is proved below; full Bernoulli logarithmic convergence is proved below; row-slice logarithmic limits remain open |
| [FiniteLabeledTrees.lean](CircularLaw/FiniteLabeledTrees.lean), [GaussianWordEdgeLabels.lean](CircularLaw/GaussianWordEdgeLabels.lean), [GaussianWordLeadingTrees.lean](CircularLaw/GaussianWordLeadingTrees.lean) | Maximal connected vertex count excludes loops and repeated unordered edges; arbitrary leading words give a labeled tree; each edge occurs exactly at its two matched positions | Leading-tree characterization now covers every direct/adjoint word order |
| [TreeEdgeCuts.lean](CircularLaw/TreeEdgeCuts.lean), [FiniteCircularCuts.lean](CircularLaw/FiniteCircularCuts.lean), [GaussianWordTreeCuts.lean](CircularLaw/GaussianWordTreeCuts.lean) | Tree-edge deletion separates endpoints; its actual side predicate switches exactly at the matched positions and equals the finite circular cut; all other matches stay on one side | Every leading Gaussian word pairing is noncrossing, with the finite wrap handled explicitly |
| [FiniteLabeledSeparators.lean](CircularLaw/FiniteLabeledSeparators.lean), [GaussianWordNoncrossingCounts.lean](CircularLaw/GaussianWordNoncrossingCounts.lean) | Noncrossing circular cuts descend to the endpoint quotient and separate individual labels; the converse forces a labeled tree and maximal exponent; every word mean and shifted even moment has the exact weighted noncrossing-count formula | Leading iff noncrossing proved; Catalan enumeration is proved below; Gaussian/circular logarithmic identification is proved below |
| [GaussianNoncrossingIntervals.lean](CircularLaw/GaussianNoncrossingIntervals.lean), [GaussianWordRestrictions.lean](CircularLaw/GaussianWordRestrictions.lean), [GaussianFirstPairRestrictions.lean](CircularLaw/GaussianFirstPairRestrictions.lean) | Every pair closes off its strict interior; the first pair also closes off the final interval. Increasing position maps reindex both pieces as shorter words, with the actual matching images, equal direct/adjoint counts and noncrossing restrictions, including empty words | First-pair restriction proved; reconstruction, count recurrence and Catalan enumeration are proved below |
| [GaussianFirstPairAssembly.lean](CircularLaw/GaussianFirstPairAssembly.lean), [GaussianFirstPairNoncrossing.lean](CircularLaw/GaussianFirstPairNoncrossing.lean), [GaussianFirstPairDecomposition.lean](CircularLaw/GaussianFirstPairDecomposition.lean) | Explicit direct/adjoint position partitions assemble two smaller matchings; every cross-interval cut preserves noncrossing; restriction and assembly are inverse in each first-partner fiber, giving the exact sigma equivalence, sum of products and empty count one | Full first-pair decomposition and count recurrence proved |
| [GaussianNoncrossingNegation.lean](CircularLaw/GaussianNoncrossingNegation.lean), [GaussianAlternatingWords.lean](CircularLaw/GaussianAlternatingWords.lean), [GaussianAlternatingCatalan.lean](CircularLaw/GaussianAlternatingCatalan.lean) | Color negation reverses the matching and preserves counts; parity parametrizes all actual fibers; odd alternating counts vanish, even counts satisfy the Catalan convolution and equal `catalan(k)=centralBinom(k)/(k+1)`; actual normalized alternating word mean limits have this value | All-order alternating Catalan enumeration proved |
| [GaussianZeroCatalanMoments.lean](CircularLaw/GaussianZeroCatalanMoments.lean) | The Gram word equals the alternating word; at zero shift only the full retained word contributes. Every actual zero-shift even singular moment converges in mean square and probability to the Catalan number, both constructed zero-shift laws have these moments, and `gaussianLeadingMomentCount(k)=catalan(k+1)` | Actual zero-shift Catalan moments proved; the beta law identification is proved below; shifted circular logarithmic identification is proved below |
| [BetaMeasureMoments.lean](CircularLaw/BetaMeasureMoments.lean), [BetaCatalanMoments.lean](CircularLaw/BetaCatalanMoments.lean) | The actual beta measure lies in the open unit interval; every natural moment is a beta-constant ratio. Gamma recurrence identifies all moments of four times beta(1/2,3/2) with the Catalan numbers and its beta constant with pi/2 | All beta moments and fixed normalization proved |
| [GaussianZeroBetaCandidate.lean](CircularLaw/GaussianZeroBetaCandidate.lean), [GaussianZeroBetaIdentification.lean](CircularLaw/GaussianZeroBetaIdentification.lean) | The scaled beta candidate has every actual compact squared-moment limit. Actual Gaussian weak convergence to its square-root image and uniqueness identify both zero-shift limits with the law of sqrt(4*X), for X distributed as beta(1/2,3/2) | Explicit transformed-beta law identification proved |
| [GaussianZeroBetaProperties.lean](CircularLaw/GaussianZeroBetaProperties.lean) | The actual zero-shift law has support in [0,2]; every strongly measurable test has the explicit beta density integral. The beta logarithm is integrable, and the actual singular logarithmic integral equals log(2) plus one-half its beta logarithmic moment | Sharp support and logarithmic reduction proved; the density form and numerical value are proved below |
| [BetaHalfMellin.lean](CircularLaw/BetaHalfMellin.lean), [BetaHalfLogMoment.lean](CircularLaw/BetaHalfLogMoment.lean) | The continuous square-root kernel has checked Mellin bounds at zero and infinity. Differentiation of the actual integral and its Gamma quotient gives the beta logarithmic moment -2*log(2)-1 | Actual logarithmic moment evaluated without derivative or integrability premises |
| [GaussianZeroLogValue.lean](CircularLaw/GaussianZeroLogValue.lean) | Both actual zero-shift Gaussian limiting laws have logarithmic integral -1/2, equal to the circular logarithmic potential at zero; the manuscript's negative-potential convention is also checked | Zero-shift Gaussian/circular logarithmic identity proved; the identity at general shifts is proved below |
| [BetaQuarterCircleChange.lean](CircularLaw/BetaQuarterCircleChange.lean), [GaussianZeroQuarterCircle.lean](CircularLaw/GaussianZeroQuarterCircle.lean) | The square map sends (0,2) bijectively onto (0,1); its Jacobian gives sqrt(4-s^2)/pi. This density defines a probability law whose nonnegative-coordinate image equals both actual zero-shift limits. Actual weak convergence, every strongly measurable test integral and the logarithmic value are checked | Actual quarter-circle density law and its logarithmic value proved |
| [GaussianSmallDistanceTails.lean](CircularLaw/GaussianSmallDistanceTails.lean), [GaussianSmallestPolynomial.lean](CircularLaw/GaussianSmallestPolynomial.lean) | Actual projected Gaussian small balls give linear squared-distance tails; negative second moments and row restriction give smallest normalized singular-value failure at most exp(1)/n below n^(-2), at every shift | Polynomial Gaussian minimum bound proved without a separate smallest-value assumption |
| [GaussianUniformQuantiles.lean](CircularLaw/GaussianUniformQuantiles.lean) | Simultaneous lower quantiles have failure at most n^2*2^(-floor(sqrt(n))), tending to zero; outside this event ranks above 2*floor(sqrt(n)) have singular value at least rank/(16*n) | Uniform Gaussian rank control |
| [BottomRankLogEntropy.lean](CircularLaw/BottomRankLogEntropy.lean), [GaussianGoodLogBounds.lean](CircularLaw/GaussianGoodLogBounds.lean), [GaussianBottomLogRates.lean](CircularLaw/GaussianBottomLogRates.lean) | Checked factorial entropy bounds control bottom negative-log sums. The lowest sqrt(n) scale has vanishing budget, and a bottom fraction eta has limiting budget eta*(log(16/eta)+1), vanishing as eta tends to zero | Actual Gaussian bottom logarithmic control |
| [NegativeLogBottomClipping.lean](CircularLaw/NegativeLogBottomClipping.lean), [GaussianNegativeLogClipping.lean](CircularLaw/GaussianNegativeLogClipping.lean) | Clipping excess is bounded by the actual bottom negative-log sum; for every positive tolerance a fixed clipping threshold makes its failure probability tend to zero, including the zero-singular-value event | Unconditional Gaussian negative clipping at every complex shift |
| [GaussianLogConvergence.lean](CircularLaw/GaussianLogConvergence.lean) | Actual Gaussian negative and positive logarithmic means, full empirical logarithms and spectral logarithmic potentials converge in probability to the constructed limiting integral at every shift; at zero the value is -1/2 | Gaussian full-log convergence proved; general-shift circular-potential identity is proved below; Bernoulli full logarithmic convergence remains open |
| [EmpiricalFullLogPrefixConvergence.lean](CircularLaw/EmpiricalFullLogPrefixConvergence.lean) | Exact prefix/bottom partition makes the negative-log difference the bottom sum; full-log convergence, uniform integrability and tight second moments give the same untruncated logarithmic limit on every prefix omitting o(n) values | General prefix deduction proved without a slow-choice requirement |
| [GaussianLogTailReduction.lean](CircularLaw/GaussianLogTailReduction.lean), [GaussianLogPrefixConvergence.lean](CircularLaw/GaussianLogPrefixConvergence.lean) | Unconditional actual Gaussian extended negative-log uniform integrability and bottom-r convergence for every r=o(n); all untruncated prefix limits, exact manuscript floors, negative sign and null prefix zero events | Gaussian tails and prefixes proved at every complex shift |
| [BernoulliGaussianPrefix.lean](CircularLaw/BernoulliGaussianPrefix.lean) | One positive decreasing fraction gives actual Gaussian and Bernoulli signed-prefix limits, supplying all Gaussian mass and support bounds by checked proofs | Actual Bernoulli weak-law transfer is supplied under `d->infinity` and `d/n->0`; full Bernoulli logarithmic convergence is proved below |
| [GaussianShiftRotation.lean](CircularLaw/GaussianShiftRotation.lean) | Actual Gaussian product law is invariant under unit multiplication; simultaneous matrix/shift rotation preserves the Gram matrix; uniqueness identifies the complete limiting singular measures and logarithmic integrals at equal-radius shifts | General-shift logarithmic identification reduces to the radial value formula proved below |
| [GaussianNoncrossingListRecursion.lean](CircularLaw/GaussianNoncrossingListRecursion.lean), [GaussianWordDerivative.lean](CircularLaw/GaussianWordDerivative.lean) | Every direct/adjoint word count satisfies the exact first-partner prefix/suffix recurrence; deleting opposite symbols obeys the noncommutative product rule and evaluates to the actual limiting Gaussian word mean | First-pair recurrence for arbitrary ordered words |
| [ScalarShiftWordEvaluation.lean](CircularLaw/ScalarShiftWordEvaluation.lean), [GaussianShiftedWordFunctional.lean](CircularLaw/GaussianShiftedWordFunctional.lean) | Finite linear expansion turns each deletion into the shifted prefix/suffix product. The resulting functional is the actual normalized trace-mean limit for every shifted word and gives the limiting singular moments on Gram words | Full scalar-shifted first-pair recurrence proved, with all multiplicities retained |
| [GaussianShiftedAlternatingRecursion.lean](CircularLaw/GaussianShiftedAlternatingRecursion.lean), [GaussianShiftedMomentSeries.lean](CircularLaw/GaussianShiftedMomentSeries.lean) | Real-shift color symmetry and exact parity reindexing give even/odd alternating recurrences. The actual limiting moment series satisfy both coupled equations and the eliminated cubic | Formal series identities proved; the analytic resolvent identification is proved below; general logarithmic value is proved below |
| [SquaredResolventAnalytic.lean](CircularLaw/SquaredResolventAnalytic.lean), [SquaredResolventMomentSeries.lean](CircularLaw/SquaredResolventMomentSeries.lean) | Actual kernel and derivative bounds justify differentiation under every compact finite nonnegative-coordinate measure. Uniform geometric domination identifies the actual Gaussian squared resolvent with the checked moment series near zero | Analyticity on the left half-plane and the convergent moment series proved |
| [PowerSeriesSums.lean](CircularLaw/PowerSeriesSums.lean), [GaussianShiftedResolventCubic.lean](CircularLaw/GaussianShiftedResolventCubic.lean) | Absolute summability validates the formal series product and cubic near zero; the analytic identity principle extends the actual resolvent cubic to the entire left half-plane | Actual resolvent cubic proved without a spectral equation hypothesis |
| [GaussianHermitizedResolvent.lean](CircularLaw/GaussianHermitizedResolvent.lean) | The actual integral of t/(t^2+s^2) is positive, is at most 1/t, satisfies the scalar Dyson equation and is bounded by one uniformly for positive t | Actual Hermitized resolvent equation proved; evaluation of the logarithmic integral is proved below |
| [HermitizedResolventDerivatives.lean](CircularLaw/HermitizedResolventDerivatives.lean), [GaussianRegularizedLogDerivative.lean](CircularLaw/GaussianRegularizedLogDerivative.lean) | Uniform kernel-derivative domination differentiates the actual resolvent and compactly supported regularized logarithmic integral. The explicit Dyson expression has the same derivative | Actual integral derivatives checked without a value premise |
| [GaussianRegularizedLogBounds.lean](CircularLaw/GaussianRegularizedLogBounds.lean), [GaussianRegularizedLogValue.lean](CircularLaw/GaussianRegularizedLogValue.lean) | The integral and explicit Dyson expression both differ from log(t) by a quantity tending to zero at infinity. Their derivative-zero difference is constant, giving the exact identity at every positive regularization | Actual regularized logarithmic value proved |
| [GaussianRegularizedLogRemoval.lean](CircularLaw/GaussianRegularizedLogRemoval.lean), [GaussianHermitizedZeroLimit.lean](CircularLaw/GaussianHermitizedZeroLimit.lean) | Absolute-log domination removes regularization. The actual Dyson equation gives limit sqrt(1-r^2) for 0<=r<1 and zero for r>=1, including the unit circle | Both zero-regularization limits proved |
| [GaussianShiftedLogValue.lean](CircularLaw/GaussianShiftedLogValue.lean), [GaussianCircularLaw.lean](CircularLaw/GaussianCircularLaw.lean) | The actual singular limiting logarithmic integral equals the uniform-disk potential at every complex shift. Full empirical logs, spectral potentials, log determinants and all vanishing-fraction prefixes converge to that value. Direct hermitization proves full bounded-Lipschitz Gaussian ESD convergence to the uniform unit disk | Gaussian circular-law comparator proved with every Gaussian hypothesis discharged; the named row-slice main theorem remains unproved |
| [BernoulliGaussianCircularPrefix.lean](CircularLaw/BernoulliGaussianCircularPrefix.lean) | One common positive antitone fraction gives both literal rounded Gaussian and Bernoulli prefixes with the actual paper circular potential as limit, and both zero events vanish | Actual Bernoulli weak-law transfer is supplied under the degree hypotheses; full logarithmic and minor upper estimates are proved below |
| [BernoulliCenteredEntryWords.lean](CircularLaw/BernoulliCenteredEntryWords.lean), [BernoulliMatrixWordMeans.lean](CircularLaw/BernoulliMatrixWordMeans.lean) | Exact centered marginal moments and actual independent-entry word integrals; all matrix-word and two-trace walk formulas; singleton cancellation and bounds by distinct-entry count | Finite probabilistic input to the sparse Bernoulli weak law proved below |
| [BernoulliNormalizedWordMeans.lean](CircularLaw/BernoulliNormalizedWordMeans.lean) | Literal mean subtraction, sparse normalization, exact normalized trace formulas and the centered shifted Gram expansion | No asymptotic Bernoulli moment limit is assumed or inferred |
| [BernoulliCenteringInterlacing.lean](CircularLaw/BernoulliCenteringInterlacing.lean), [BernoulliCenteringDistribution.lean](CircularLaw/BernoulliCenteringDistribution.lean) | Constant-entry mean has rank at most one; both one-index singular interlacings; actual empirical mass below every threshold changes by at most `1/n` | Deterministic centering comparison for every sample, degree and shift |
| [BernoulliWalkVertexBounds.lean](CircularLaw/BernoulliWalkVertexBounds.lean), [FiniteKernelColorings.lean](CircularLaw/FiniteKernelColorings.lean) | Connected visited-vertex graph; vertex count at most entry count plus one; maximal patterns are trees with nonloop labels; exact equality-pattern coloring count and its normalized limit | Dimension-counting ingredients; Gaussian leading-pattern identification and concentration are proved below |
| [FiniteKernelPartition.lean](CircularLaw/FiniteKernelPartition.lean), [BernoulliWalkPatterns.lean](CircularLaw/BernoulliWalkPatterns.lean) | Finitely many exact vertex kernels; grouping of every actual centered trace mean by its canonical quotient walk, with exact falling-factorial coefficients; singleton cancellation, variance factors and vertex/entry bounds | Pattern set depends on word length, independently of matrix dimension |
| [SparsePatternPowerLimits.lean](CircularLaw/SparsePatternPowerLimits.lean), [BernoulliPatternMeanLimits.lean](CircularLaw/BernoulliPatternMeanLimits.lean) | Separate dimension and sparse-degree power budgets; every nonleading even pattern vanishes and every leading paired pattern contributes one; actual even word-mean limits | Requires `d->infinity` and `d/n->0`; Gaussian count identification is proved below |
| [BernoulliAllWordMeanLimits.lean](CircularLaw/BernoulliAllWordMeanLimits.lean) | Every actual centered normalized direct/adjoint word mean converges; odd words tend to zero and the empty word to one | Mean convergence; concentration is proved below |
| [BernoulliShiftedMomentMeanLimits.lean](CircularLaw/BernoulliShiftedMomentMeanLimits.lean) | Actual complex word means are real; finite scalar-shift assembly proves convergence of every centered shifted even singular-moment mean to a finite nonnegative value, at every complex shift | Gaussian identification, concentration and the Bernoulli weak singular law are proved below |
| [BernoulliWordCovarianceWeights.lean](CircularLaw/BernoulliWordCovarianceWeights.lean), [ClosedTwoWalkGraph.lean](CircularLaw/ClosedTwoWalkGraph.lean), [BernoulliTwoWalkPatterns.lean](CircularLaw/BernoulliTwoWalkPatterns.lean) | Disjoint entry supports cancel in covariance; joint singletons vanish; surviving weights are bounded by twice the parameter power; sharing an ordered entry connects the joint graph and gives `v<=e+1` | Exact finite covariance ingredients, with all shared vertices retained |
| [BernoulliTwoWordCovariance.lean](CircularLaw/BernoulliTwoWordCovariance.lean), [BernoulliNormalizedWordCovariance.lean](CircularLaw/BernoulliNormalizedWordCovariance.lean) | Actual covariance is an exact falling-factorial pattern sum; each surviving even contribution is bounded by `2/n`, with an extra inverse square-root degree factor for odd length; every fixed word covariance tends to zero | Requires `d->infinity` and `d/n->0`; no Gaussian identification is assumed |
| [BernoulliWordConcentration.lean](CircularLaw/BernoulliWordConcentration.lean), [BernoulliShiftedMomentConcentration.lean](CircularLaw/BernoulliShiftedMomentConcentration.lean) | Every actual centered word converges in mean square and probability; every actual centered shifted even singular moment converges in probability to its scalar-shifted pattern-count limit | All fixed complex shifts and even orders; Gaussian count identification and weak-law passage are proved below |
| [ClosedWalkTreeOrientation.lean](CircularLaw/ClosedWalkTreeOrientation.lean), [BernoulliLeadingPartners.lean](CircularLaw/BernoulliLeadingPartners.lean) | Deleting an edge of a maximal visited tree forces both orientations in the closed walk; each leading ordered-entry fiber has exactly two opposite symbols, giving a unique involutive partner | Exact leading Bernoulli pairing construction |
| [BernoulliLeadingGaussianKernel.lean](CircularLaw/BernoulliLeadingGaussianKernel.lean), [GaussianLeadingBernoulliPatterns.lean](CircularLaw/GaussianLeadingBernoulliPatterns.lean) | The matching-generated equivalence relation equals the original Bernoulli vertex kernel; every maximal Gaussian pairing has two-occurrence entries and yields a leading Bernoulli kernel | Both directions proved with exact quotient cardinalities |
| [BernoulliGaussianWordCounts.lean](CircularLaw/BernoulliGaussianWordCounts.lean) | Exact bijection identifies every Bernoulli word count with its Gaussian count, including unbalanced and empty words; all centered words and shifted even singular moments converge in probability to the Gaussian limits | Actual centered moment identification at every fixed complex shift |
| [PolynomialMomentTailApproximation.lean](CircularLaw/PolynomialMomentTailApproximation.lean), [CompactTargetMomentConvergence.lean](CircularLaw/CompactTargetMomentConvergence.lean) | A higher moment controls polynomial approximation errors outside a chosen interval; all moment limits equal to a compact target imply convergence in probability of every bounded continuous test mean | No compact-support assumption on the finite samples |
| [BernoulliCenteredWeakLimit.lean](CircularLaw/BernoulliCenteredWeakLimit.lean) | Actual centered squared singular moments give bounded-continuous convergence to the compact Gaussian squared law; square-root pushforward proves the centered shifted weak singular law | Under `d->infinity` and `d/n->0`, at every complex shift |
| [ClippedInterlacingMeanBounds.lean](CircularLaw/ClippedInterlacingMeanBounds.lean), [InterlacedContinuousMeanComparison.lean](CircularLaw/InterlacedContinuousMeanComparison.lean), [InterlacedEmpiricalWeakTransfer.lean](CircularLaw/InterlacedEmpiricalWeakTransfer.lean) | One-index interlacing bounds clipped mean distance by `2*S/n`; uniform continuity and a compact-target cutoff transfer every bounded continuous test through the actual rank-one mean | General empirical weak-convergence transfer proved |
| [BernoulliGaussianWeakTransfer.lean](CircularLaw/BernoulliGaussianWeakTransfer.lean) | The actual uncentered sparse Bernoulli singular law converges weakly in probability to the constructed Gaussian law at every complex shift | SSS25 Fact 10.2 and Bernoulli hermitization part (i) proved; part (ii) is proved below |
| [SparseRealPatternPowerLimits.lean](CircularLaw/SparseRealPatternPowerLimits.lean), [ParameterBernoulliWordMeans.lean](CircularLaw/ParameterBernoulliWordMeans.lean), [ParameterBernoulliMeanLimits.lean](CircularLaw/ParameterBernoulliMeanLimits.lean) | Real effective degree `m*p`; exact actual word integrals and pattern sums; every centered word mean has its Gaussian limit for growing dimensions, `p->0` and `m*p->infinity` | No integer effective-degree assumption |
| [ParameterBernoulliWordCovariance.lean](CircularLaw/ParameterBernoulliWordCovariance.lean), [ParameterBernoulliWordConcentration.lean](CircularLaw/ParameterBernoulliWordConcentration.lean), [ParameterBernoulliShiftedMoments.lean](CircularLaw/ParameterBernoulliShiftedMoments.lean) | Exact parameter-dependent covariance sum retains every shared entry; dimension and real-degree losses prove mean-square word convergence and probability convergence of every shifted even singular moment | Actual arbitrary-parameter Bernoulli concentration proved |
| [ParameterBernoulliWeakLimit.lean](CircularLaw/ParameterBernoulliWeakLimit.lean) | Compact-target moments and rank-one centering comparison prove the actual uncentered weak singular law for every sparse Bernoulli parameter sequence and growing dimension sequence | Effective-degree normalization, at every fixed complex shift |
| [BernoulliPrincipalMinorLaw.lean](CircularLaw/BernoulliPrincipalMinorLaw.lean), [BernoulliPrincipalMinorWeakLimit.lean](CircularLaw/BernoulliPrincipalMinorWeakLimit.lean) | Coordinate restriction preserves the ambient independent Bernoulli probability; positive dimension ratio makes the minor effective degree grow; the actual floor-defined minor has its effective-degree weak law; exact finite rescaling retains the source ambient normalization | Effective-degree law and exact finite normalization; the ambient-normalized passage is proved below |
| [SquareSingularPerturbationBounds.lean](CircularLaw/SquareSingularPerturbationBounds.lean), [RelativeEmpiricalWeakTransfer.lean](CircularLaw/RelativeEmpiricalWeakTransfer.lean), [ScaledEmpiricalWeakTransfer.lean](CircularLaw/ScaledEmpiricalWeakTransfer.lean) | Adjoint norm bounds compare ordered singular values; scalar multiplication scales them exactly and scalar shifts change them by at most the shift norm; relative errors vanish in empirical weak tests using the compact limiting support | Checked varying scales and shifts without a samplewise top-value bound |
| [BernoulliPrincipalMinorAmbientWeakLimit.lean](CircularLaw/BernoulliPrincipalMinorAmbientWeakLimit.lean), [GaussianMinorLimitProperties.lean](CircularLaw/GaussianMinorLimitProperties.lean) | The actual ambient-normalized principal minor converges weakly to the scaled Gaussian law; linear mass near zero, compact support, finite logarithmic integral and exact circular scaling correction; limiting negative logarithm tends to the full circular value as the ratio tends to one | Includes every fixed positive minor ratio and every complex shift |
| [IndexedRetainedPrefixSmallValues.lean](CircularLaw/IndexedRetainedPrefixSmallValues.lean), [BernoulliPrincipalMinorSmallValues.lean](CircularLaw/BernoulliPrincipalMinorSmallValues.lean) | Weak-law lower bounds permit varying array dimensions; the literal retained minor prefix omits at least epsilon/4 of the minor and has a fixed positive lower singular-value bound with probability tending to one; retained-zero probability vanishes | The common logarithmic-prefix limit is proved below; the full-to-minor upper estimate remains open |
| [BernoulliPrincipalMinorSecondMoment.lean](CircularLaw/BernoulliPrincipalMinorSecondMoment.lean) | Actual restricted ambient-law minor second moment, uniform expectation bound and probability tail bound with source normalization | Supplies upper-log tail control for the actual minor |
| [LinearMassLogClipping.lean](CircularLaw/LinearMassLogClipping.lean), [GaussianMinorUniformLogBounds.lean](CircularLaw/GaussianMinorUniformLogBounds.lean) | Exponential-tail integration and negative-log clipping errors from linear small-value mass; uniform scaled Gaussian clipping and support bounds for ratios at least one half | Zero mass is derived and the totalized logarithm at zero is handled almost everywhere |
| [MinorLogPrefixDeviation.lean](CircularLaw/MinorLogPrefixDeviation.lean), [MinorLogarithmicStages.lean](CircularLaw/MinorLogarithmicStages.lean), [BernoulliMinorLogStageBounds.lean](CircularLaw/BernoulliMinorLogStageBounds.lean) | Signed prefix error from clipping and second moments; exact ambient-denominator minor T identity; vanishing stage tolerances, floor errors and actual probability bounds | Retains both literal floors and controls small values, large values and clipped-test errors |
| [BernoulliCommonMinorLogPrefix.lean](CircularLaw/BernoulliCommonMinorLogPrefix.lean) | The literal actual Bernoulli full T1 and minor T converge to the circular potential along one common positive antitone slow fraction; minor retained-zero probability vanishes; optional eventual constraints are retained | Every prefix-limit premise is supplied under the sparse degree hypotheses |
| [ExposureProcessDrift.lean](CircularLaw/ExposureProcessDrift.lean), [ExposureProcessCompletion.lean](CircularLaw/ExposureProcessCompletion.lean), [HalfIntegerExposureDrift.lean](CircularLaw/HalfIntegerExposureDrift.lean) | Full SSS25 Lemma 8.4: conditional exponential moment and terminal completion probability for an adapted half-integer height, with the moving barrier and exact growth/initial bounds; includes q=0 | Independent proof of the drift lemma; small-dimension projection and graph inputs remain open |
| [ExposureGoodEventCoupling.lean](CircularLaw/ExposureGoodEventCoupling.lean) | Killing height on nested currently measurable good-event failures preserves conditional drift; terminal failure is at most the final good-event failure plus 4*q^(1/8); varying-space completion follows when both errors vanish | Checks the coupling in SSS25 Lemma 8.1; actual exposure-process estimates remain to be supplied |
| [MatrixSingularVolumes.lean](CircularLaw/MatrixSingularVolumes.lean), [LeadingRowSingularCompression.lean](CircularLaw/LeadingRowSingularCompression.lean) | Coisometric row compression bounds the actual Gram determinant by the leading singular product squared; sorted left spectral directions give the exact leading Gram determinant | Reindexing matches the actual sorted eigenvalues |
| [RowKernelProjection.lean](CircularLaw/RowKernelProjection.lean), [InsertedRowSingularVolume.lean](CircularLaw/InsertedRowSingularVolume.lean) | The unregularized inverse-Gram matrix equals the actual kernel orthogonal projection; inserting a row multiplies the Gram determinant by the projection norm squared | Inverse-Gram identity assumes full row rank; singular-product proof treats zero products separately |
| [RowAdditionSingularProducts.lean](CircularLaw/RowAdditionSingularProducts.lean), [LeadingRowKernelGeometry.lean](CircularLaw/LeadingRowKernelGeometry.lean) | For r<=n, the leading r+1 new singular product dominates the old leading r product times the actual leading-row kernel projection norm; nonzero old product gives dimension m-r and a next-singular-value near-kernel bound | Kernel-projection form used in SSS25 Lemma 7.2; the r=n endpoint is the actual full matrix kernel |
| [RowAdditionSingularInterlacing.lean](CircularLaw/RowAdditionSingularInterlacing.lean), [RowAdditionLogIncrement.lean](CircularLaw/RowAdditionLogIncrement.lean) | Actual row-deletion coisometry, large-next-singular-value branch and normalized logarithmic increment; step failure is contained in the projection-small event | Positive old product is required for logarithms; a probability bound under basis spread is supplied below |
| [RectangularAdjointSingularValues.lean](CircularLaw/RectangularAdjointSingularValues.lean), [ReindexedMatrixSingularValues.lean](CircularLaw/ReindexedMatrixSingularValues.lean) | The row and column Gram spectra differ only by trailing zero roots; common ordered singular positions agree under adjoint, and all positions are preserved by finite row/column permutations | Arbitrary finite dimensions and rank deficiency included |
| [ColumnAdditionSingularProducts.lean](CircularLaw/ColumnAdditionSingularProducts.lean), [ColumnAdditionLogIncrement.lean](CircularLaw/ColumnAdditionLogIncrement.lean) | Column insertion has the actual projection-times-old-product bound, both normalized log branches, failure-event containment and leading-kernel geometry | Product bound permits zero old products; log estimates require positive old products |
| [LastIndexMatrixInsertion.lean](CircularLaw/LastIndexMatrixInsertion.lean) | Literal deletion of the last row or column matches insertion after a checked index permutation; retained log steps and same-prefix monotonicity follow | Actual last indices and finite dimensions; alternating process assembly remains open |
| [WeightedBernoulliSymmetrization.lean](CircularLaw/WeightedBernoulliSymmetrization.lean), [WeightedBernoulliSmallBall.lean](CircularLaw/WeightedBernoulliSmallBall.lean) | Exact two-atom symmetrized moments and the actual weighted cube law give scalar probability at most `(48*exp(1)/pi)*(t/rho)/sqrt(k*p)` | `0<p<=1/2`, at least k nonzero coefficients of modulus at least rho, and `t>=rho/2`; arbitrary complex center |
| [BernoulliProjectionSmallBall.lean](CircularLaw/BernoulliProjectionSmallBall.lean), [BernoulliExposureSmallBall.lean](CircularLaw/BernoulliExposureSmallBall.lean) | Projection energy forces half the basis coordinates to be small; the actual Bernoulli projection and row/column log-step failure probabilities are bounded by `2*C*(t/rho)/sqrt(k*p)` under uniform basis spread | The proved basis construction below supplies uniform spread; compatible radius is explicit |
| [RademacherLinearMoments.lean](CircularLaw/RademacherLinearMoments.lean) | Actual fair-sign complex sums have second moment equal to coefficient energy, fourth moment at most five times its square, and mean norm at least one eighth of its square root | Moment input to basis construction |
| [FlatFourierBasis.lean](CircularLaw/FlatFourierBasis.lean), [SignedFourierMixing.lean](CircularLaw/SignedFourierMixing.lean) | A flat Fourier matrix and diagonal fair signs give a genuine orthonormal basis for every sample, with exact coordinate coefficient energies and mean-norm bounds | Every positive dimension, including dimension one |
| [FourierBasisMass.lean](CircularLaw/FourierBasisMass.lean), [ExtremalBasisMass.lean](CircularLaw/ExtremalBasisMass.lean) | Total coordinate mass has average at least `h*sqrt(h)/8`; compact orthonormal frames give a basis maximizing that mass | Finite-dimensional complex subspaces |
| [BasisPairRotation.lean](CircularLaw/BasisPairRotation.lean), [UniformBasisMass.lean](CircularLaw/UniformBasisMass.lean), [UniformBasisSpread.lean](CircularLaw/UniformBasisSpread.lean) | Pair rotation makes maximizing-basis masses comparable; every vector of a suitable basis has coordinate mass at least `sqrt(h)/32` and at least `h/4096` coordinates of modulus at least `sqrt(h)/(64*n)` | Checked uniform spread-basis existence with absolute constants |
| [BernoulliSubspaceSmallBall.lean](CircularLaw/BernoulliSubspaceSmallBall.lean) | Actual projection and row/column log-step failure bounds use the proved spread basis, with `k=ceil(h/4096)` and `rho=sqrt(h)/(64*n)` | Positive subspace dimension and compatible radius; small-dimension graph-spread regime, graph events and process assembly are supplied below |
| [BernoulliProjectionRadius.lean](CircularLaw/BernoulliProjectionRadius.lean) | Enlarging the scalar radius supplies the actual projection bound `C*(kappa+1/sqrt(h*p))` at every requested radius `kappa*sqrt(p)*h*sqrt(h)/n` | Ambient coordinate count at most n; no assumed probability estimate |
| [BernoulliLargeProjection.lean](CircularLaw/BernoulliLargeProjection.lean) | Bernoulli specialization of SSS25 Lemma 6.2: at radius `kappa*sqrt(d)*h^(3/2)*n^(-3/2)`, actual probability is at most `C*(kappa+d^(-1/4))`; the closed `BernoulliLargeProjectionLemma` has a proof | `d=n*p>=1`, `h>=n*d^(-1/4)`, `0<p<=1/2`, ambient dimensions at most n, arbitrary shifts and conjugation; explicit absolute C |
| [BernoulliLargeExposure.lean](CircularLaw/BernoulliLargeExposure.lean) | Actual row/column logarithmic failure probabilities satisfy the large-dimension projection bound | Positive old singular product and comparison of the log-step threshold with the projection radius; small-dimension regime and process assembly are supplied below |
| [UniqueNeighbourhoodGeometry.lean](CircularLaw/UniqueNeighbourhoodGeometry.lean) | Restricted-vector image lower bound on both kinds of unique-neighbourhood row | Actual rectangular matrix, embedded diagonal shift, head-coordinate lower bound and shift norm at least beta |
| [ShiftedGraphBudgets.lean](CircularLaw/ShiftedGraphBudgets.lean) | Actual middle-support row count and shifted row-mass/tail-image bounds | Column support counts include at most one embedded diagonal row per column |
| [UniqueNeighbourhoodAmplification.lean](CircularLaw/UniqueNeighbourhoodAmplification.lean) | Head/middle/tail decomposition forces many large image coordinates | Explicit actual expansion, heavy-row and middle-column budgets; tail radius compatibility |
| [GraphCoordinateGap.lean](CircularLaw/GraphCoordinateGap.lean) | The source fifth-power row threshold and seventh-power gap imply image spread at the literal one-based ranks | `0<beta<=1`, `d>=4`, positive valid ranks, explicit graph counts and middle size `g-1` |
| [GraphNearKernelGap.lean](CircularLaw/GraphNearKernelGap.lean) | Image spread gives a squared-norm lower bound and excludes coordinate gaps for near-kernel vectors | Actual graph-count hypotheses and explicit small-image energy; the source growth and iteration are supplied below |
| [GraphGrowthBudget.lean](CircularLaw/GraphGrowthBudget.lean) | The actual ceiling growth function supplies the middle-support budget from the uniform column-degree condition | Explicit constant `graphGrowthConstant(K+1)=4096*(K+2)^2`; logarithmic range and middle size `g-1` |
| [SourceGraphGap.lean](CircularLaw/SourceGraphGap.lean) | Coordinate-gap image spread and near-kernel no-gap bounds from uniform actual graph budgets | Uniform column-degree, unique-neighbourhood and heavy-row events; no assumed middle budget |
| [GraphGrowthIteration.lean](CircularLaw/GraphGrowthIteration.lean) | Actual integer recurrence, positive ranks and first exit in at most `(4*C+2)*log(n/k)^4` steps | `C>=1`, `d>=1`, positive starting rank and terminal scale with `log(n/u)>=1` |
| [SourceGraphGrowthRange.lean](CircularLaw/SourceGraphGrowthRange.lean) | Exact terminal scale `n*log(log d)/(2*d)` and automatic finite next-rank bounds | `d>=exp(exp(1))`, positive n; the next rank is at most twice the current rank |
| [GraphNearKernelIteration.lean](CircularLaw/GraphNearKernelIteration.lean) | Source terminal coordinate-gap step and actual iterated vector spread beyond the terminal rank | Uniform graph events, initial modulus and an explicit squared-image norm threshold; ranks and growth are proved |
| [GraphSubspaceSmallBall.lean](CircularLaw/GraphSubspaceSmallBall.lean) | The proved spread basis is amplified by graph iteration or already has sufficient spread; at the source terminal scale actual Bernoulli projection probability is at most `4*C_scalar/sqrt(log(log d))` | Nonzero near-kernel subspace, ambient dimension at most n, uniform graph events, explicit energy and projection-radius comparisons; arbitrary deterministic center |
| [GraphLeadingKernel.lean](CircularLaw/GraphLeadingKernel.lean) | The actual leading-row kernel has its proved uniform near-kernel estimate at the next singular scale, including scale zero at full row rank; its projection probability satisfies the terminal graph bound | Nonzero old singular product, positive remaining dimension, actual graph events and scalar energy/radius comparisons |
| [BernoulliGraphExposure.lean](CircularLaw/BernoulliGraphExposure.lean) | A failed row or adjoint-column log step forces the actual singular scale below its threshold; actual failure probabilities satisfy the terminal graph bound | Positive old product, graph events and two explicit threshold comparisons; no assumed basis or uniform near-kernel estimate |
| [GraphProjectionThreshold.lean](CircularLaw/GraphProjectionThreshold.lean) | One scalar threshold implies both graph energy and projection-radius comparisons; its exact exponential cost cancels the square roots of dimension | Positive dimension and radius, seed count at least `h/4096`, positive seed logarithm, `0<beta<=1`, `d>=4` |
| [GraphProjectionCost.lean](CircularLaw/GraphProjectionCost.lean) | The exact graph threshold cost is bounded by a fifth-power envelope and then by the source degree/remaining-size eighth powers | Global remaining size at most nine local dimensions; explicit growth and beta coefficient |
| [SourceGraphProjectionThreshold.lean](CircularLaw/SourceGraphProjectionThreshold.lean) | Integer guard and small-rank range discharge the raw source-power energy/radius comparisons on the actual leading-row kernel | Guard `(N-m)/8<m-r`, `d>=exp(4)`, remaining size at most `N*d^(-1/4)`; retained-rank convention |
| [BernoulliSourceGraphExposure.lean](CircularLaw/BernoulliSourceGraphExposure.lean) | Actual raw-matrix row and adjoint-column log failures satisfy the graph probability bound with scalar comparisons proved | Graph budgets, integer guard and small-rank range; explicit source-power coefficient |
| [SourceLargeProjection.lean](CircularLaw/SourceLargeProjection.lean) | Completing a square controls the raw squared-log threshold; the inverse dimension estimate permits the guard's factor nine | Actual Bernoulli law and nonzero subspace; remaining size at least `N*d^(-1/4)` |
| [BernoulliSourceExposure.lean](CircularLaw/BernoulliSourceExposure.lean) | Both actual raw-matrix log-step branches have one uniform failure bound tending to zero with degree | Positive old product, guard and graph budgets; normalized log-prefix transfer is separate |
| [NormalizedGraphThreshold.lean](CircularLaw/NormalizedGraphThreshold.lean) | Doubling the explicit source-power coefficient absorbs `sqrt(d)` and proves both scalar comparisons for normalized projection thresholds | Guarded small-rank range and actual kernel dimension; no dropped degree factor |
| [NormalizedLargeProjection.lean](CircularLaw/NormalizedLargeProjection.lean) | Actual projection at `sqrt(d)*exp(-log(N/g)^2)` has probability at most `C_large*(epsilon+3*d^(-1/4))` | Remaining fraction at most epsilon, `log(N/g)>=4`, global size at most nine local dimensions |
| [NormalizedSourceProjection.lean](CircularLaw/NormalizedSourceProjection.lean) | Both normalized source-threshold branches give an actual leading-kernel projection error tending to zero with epsilon and growing degree | Actual next singular scale below the projection threshold, guard, graph budgets and `epsilon<=exp(-4)`; normalized insertion process remains open |
| [RectangularSingularScaling.lean](CircularLaw/RectangularSingularScaling.lean) | Actual ordered singular values scale by the scalar norm for arbitrary finite rectangular matrices, including zero scalars; positive degree scaling divides by `sqrt(d)` | Includes the disjoint-union row type used by insertion |
| [InsertionDegreeNormalization.lean](CircularLaw/InsertionDegreeNormalization.lean) | Actual inserted matrices and retained products scale exactly; row and column log prefixes acquire the rank times `log(sqrt(d))` correction | Product identities include singular matrices; log identities require nonzero retained products |
| [NormalizedInsertionLogIncrement.lean](CircularLaw/NormalizedInsertionLogIncrement.lean) | Projection and next-singular-value branches prove positive normalized new products and actual normalized log steps; failure, including a zero new product, is contained in projection smallness | Positive old product and degree; ambient log denominator positive |
| [NormalizedSourceExposure.lean](CircularLaw/NormalizedSourceExposure.lean) | Both actual normalized Bernoulli insertion directions satisfy the source probability bound without an assumed singular-scale condition | Guard, remaining-fraction range and deterministic graph budgets; simultaneous graph probabilities are supplied below; adapted process assembly is proved below |
| [NormalizedLogPowerSums.lean](CircularLaw/NormalizedLogPowerSums.lean) | Actual finite sums of logarithmic powers divided by N are at most `2*(2*k)^k*sqrt(L/N)`; subset sums obey the same bound | Positive power, positive N and `L<=N`; telescoping inverse square roots |
| [TwoBranchLogSums.lean](CircularLaw/TwoBranchLogSums.lean) | The actual two-branch finite schedule has error at most `32*sqrt(L/N)+2*B*16^8*sqrt(theta)` | Literal cutoff `floor(N*theta)`, `0<=theta<=1`, nonnegative small-branch coefficient |
| [SourceNormalizedLogError.lean](CircularLaw/SourceNormalizedLogError.lean) | The actual source schedule and literal final-rank sum have bound `32*sqrt(L/N)+C(K,beta)*log(d)^8*d^(-1/8)`, tending to zero | Shrinking remaining fraction and growing degree; no asymptotic replacement of ranks or cutoff |
| [LastIndexDegreeNormalizedSteps.lean](CircularLaw/LastIndexDegreeNormalizedSteps.lean) | Actual last-row and last-column normalized steps preserve positive retained products; keeping the same rank cannot increase the normalized prefix | Checked reindexing, projection and next-singular-value branches; positive old products |
| [BernoulliMinorUpperProbabilityReduction.lean](CircularLaw/BernoulliMinorUpperProbabilityReduction.lean) | Full Bernoulli logarithmic convergence follows from an upper estimate whose deterministic and probability errors both vanish with the fraction | One common slow choice preserves the proved prefix limits; the actual upper estimate is proved below |
| [BernoulliSubsetCountLaplace.lean](CircularLaw/BernoulliSubsetCountLaplace.lean), [BernoulliColumnSubsetCounts.lean](CircularLaw/BernoulliColumnSubsetCounts.lean) | Exact Bernoulli subset exponential moments, upper tails and actual rectangular column support counts | Actual product law, including endpoint probabilities; arbitrary fixed column sets |
| [ColumnDegreeEntropyBounds.lean](CircularLaw/ColumnDegreeEntropyBounds.lean), [BernoulliColumnDegreeBudget.lean](CircularLaw/BernoulliColumnDegreeBudget.lean) | Entropy and geometric summation give actual uniform column-degree budget failure probability at most `N^(-3)` with constant eight | Positive ambient N, row/column cardinalities at most N, effective degree `d=N*p>=1` |
| [HeavyRowsFromColumnDegree.lean](CircularLaw/HeavyRowsFromColumnDegree.lean), [ColumnDegreeRestriction.lean](CircularLaw/ColumnDegreeRestriction.lean) | Total row mass and the source fifth-power threshold give the actual heavy-row budget; injective row/column restriction preserves the column budget | Unit-bounded entries, `d>=1`, `4*K<=d`, `0<beta<=1`, column cardinality at most the ambient size |
| [BernoulliGraphDegreeProbability.lean](CircularLaw/BernoulliGraphDegreeProbability.lean) | Column-degree and heavy-row budgets hold together for every restriction outside one event of probability at most `N^(-3)` | Actual square/sparse Bernoulli laws, `d>=32` including `d>=exp(4)`; unique-neighbourhood expansion probabilities are supplied below |
| [BernoulliAdjointLaw.lean](CircularLaw/BernoulliAdjointLaw.lean), [BernoulliBidirectionalGraphDegree.lean](CircularLaw/BernoulliBidirectionalGraphDegree.lean) | Actual adjoint event probabilities agree; both orientations and all restrictions obey the graph degree budgets outside one `2*N^(-3)` event | Actual square/sparse laws, effective degree at least 32, `0<beta<=1` |
| [BernoulliRowPatterns.lean](CircularLaw/BernoulliRowPatterns.lean), [BernoulliRowProductLaw.lean](CircularLaw/BernoulliRowProductLaw.lean), [BernoulliUniqueRowLaw.lean](CircularLaw/BernoulliUniqueRowLaw.lean) | Exact selected zero/single-one probabilities, row product law and actual graph-row membership | Includes empty sets and endpoint probabilities; graph membership uses `0<beta<=1` |
| [BernoulliUniqueCountLaplace.lean](CircularLaw/BernoulliUniqueCountLaplace.lean), [BernoulliUniqueCountStructure.lean](CircularLaw/BernoulliUniqueCountStructure.lean) | Actual unique-neighbourhood mean, exponential moment and fixed-set lower tails retain both diagonal and outside rows | Arbitrary finite rectangular row/column types and diagonal embedding; no assumed independence or concentration bound |
| [BernoulliUniqueSmallSetFactors.lean](CircularLaw/BernoulliUniqueSmallSetFactors.lean), [BernoulliSquareSmallSetExpansion.lean](CircularLaw/BernoulliSquareSmallSetExpansion.lean), [BernoulliSquareSmallExpansionProbability.lean](CircularLaw/BernoulliSquareSmallExpansionProbability.lean) | Uniform actual square unique expansion for every set with `|S|>=k>0` and `|S|*p<=1/2`, except with probability at most `2*exp(-d*k/16)` | Effective degree `d=N*p>=exp(64)` |
| [BernoulliAmbientSmallSetExpansion.lean](CircularLaw/BernoulliAmbientSmallSetExpansion.lean), [BernoulliRectangularColumnSets.lean](CircularLaw/BernoulliRectangularColumnSets.lean), [BernoulliSmallSetFamilyExpansion.lean](CircularLaw/BernoulliSmallSetFamilyExpansion.lean), [BernoulliExposureSmallSetCardinality.lean](CircularLaw/BernoulliExposureSmallSetCardinality.lean), [FiniteSmallSetExpansionUnion.lean](CircularLaw/FiniteSmallSetExpansionUnion.lean), [BernoulliExposureSmallExpansionProbability.lean](CircularLaw/BernoulliExposureSmallExpansionProbability.lean) | Small-set expansion at the original ambient normalization; square-minor failure at most `2*exp(-d*k/16)` and one-column rectangular failure at most `4*exp(-d*k/16)` | At least `3*N/4` rows, `d=N*p>=exp(64)`, `k>0`, `0<beta<=1`; the unmatched column is counted separately |
| [BernoulliLargeSetMean.lean](CircularLaw/BernoulliLargeSetMean.lean), [SourceLargeSetExpansionBounds.lean](CircularLaw/SourceLargeSetExpansionBounds.lean), [BernoulliSourceLargeSetExpansion.lean](CircularLaw/BernoulliSourceLargeSetExpansion.lean), [BernoulliSourceLargeExpansionProbability.lean](CircularLaw/BernoulliSourceLargeExpansionProbability.lean), [BernoulliSourceUniqueExpansionProbability.lean](CircularLaw/BernoulliSourceUniqueExpansionProbability.lean) | Larger-set mean at least `N/(4*log(d))`; full source expansion budget fails with probability at most the small-set bound plus `N*exp(-N/(64*log(d)))` | `d>=exp(1024)`, `p<=1/2`, at most N columns and at least `3*N/4` rows; square and one-column rectangular exposure laws |
| [BernoulliRectangularRestrictionLaw.lean](CircularLaw/BernoulliRectangularRestrictionLaw.lean), [BernoulliRestrictedUniqueExpansion.lean](CircularLaw/BernoulliRestrictedUniqueExpansion.lean) | Exact coordinate marginal and matrix identity; full expansion probability bounds for each specified restriction of the actual ambient matrix or its adjoint | Simultaneous schedule bounds are supplied below; adapted assembly is proved below |
| [SourceExposureExpansionSeed.lean](CircularLaw/SourceExposureExpansionSeed.lean), [BlockedExpansionFailureSums.lean](CircularLaw/BlockedExpansionFailureSums.lean) | Positive deterministic seed covers the actual guarded leading kernel; blocked geometric summation retains a constant total seed-error factor | Literal natural-number barrier and coordinate-count ceiling |
| [SourceExposureUniqueEvents.lean](CircularLaw/SourceExposureUniqueEvents.lean), [SourceExposureGraphFailureRates.lean](CircularLaw/SourceExposureGraphFailureRates.lean) | All relevant square and rectangular prefixes in both orientations obey the graph budgets outside one event with probability tending to zero | `d=N*p>=exp(1024)`, `p<=1/2`, `0<beta<=1`; degree, heavy rows and full unique expansion |
| [FiniteFreshConditionalExpectation.lean](CircularLaw/FiniteFreshConditionalExpectation.lean), [BernoulliFreshConditionalExpectation.lean](CircularLaw/BernoulliFreshConditionalExpectation.lean), [BernoulliPrefixFreshLaw.lean](CircularLaw/BernoulliPrefixFreshLaw.lean) | Conditional expectation fixes the exposed past and averages the independent actual fresh row or column law | Disjoint injective ambient entry blocks; arbitrary past-dependent failure events |
| [SourceConditionalInsertion.lean](CircularLaw/SourceConditionalInsertion.lean) | Actual next-row and next-column conditional normalized failure bounds allow a retained rank and shift vector depending on the current prefix | Explicit pointwise graph, positive-product, barrier and fraction conditions on the past event; concrete greedy conditional drift is proved below |
| [BernoulliPrefixFiltration.lean](CircularLaw/BernoulliPrefixFiltration.lean), [AlternatingPrefixSchedule.lean](CircularLaw/AlternatingPrefixSchedule.lean), [SourcePrefixGraphBudgets.lean](CircularLaw/SourcePrefixGraphBudgets.lean), [SourceProgressiveGraphEvents.lean](CircularLaw/SourceProgressiveGraphEvents.lean) | Actual alternating prefix filtration and measurable nested graph events with uniformly vanishing failure | Current graph-event adaptation proved |
| [WideBarrierExposureDrift.lean](CircularLaw/WideBarrierExposureDrift.lean), [WideBarrierExposureCompletion.lean](CircularLaw/WideBarrierExposureCompletion.lean), [WideBarrierGoodEventCoupling.lean](CircularLaw/WideBarrierGoodEventCoupling.lean), [AlternatingRetainedHeight.lean](CircularLaw/AlternatingRetainedHeight.lean) | Auxiliary barrier fits the strict insertion guard; terminal height bound is good-event failure plus `16*q^(1/8)` | Concrete drift is proved below |
| [GreedyPrefixRetainedRank.lean](CircularLaw/GreedyPrefixRetainedRank.lean), [RectangularRetainedPrefixMonotonicity.lean](CircularLaw/RectangularRetainedPrefixMonotonicity.lean), [GreedyPrefixLogControl.lean](CircularLaw/GreedyPrefixLogControl.lean), [GreedyTerminalLogBound.lean](CircularLaw/GreedyTerminalLogBound.lean) | Actual adapted greedy policy, positive products and cumulative log bound; terminal rank N gives the checked omitted-fraction error | Initial positive-product assumption and terminal-rank event retained; finite prefix estimate is proved below; normalized manuscript asymptotics remain open |
| [BernoulliPrefixInsertionViews.lean](CircularLaw/BernoulliPrefixInsertionViews.lean), [BernoulliPrefixNormalizedFailure.lean](CircularLaw/BernoulliPrefixNormalizedFailure.lean), [AlternatingPrefixInsertionIdentities.lean](CircularLaw/AlternatingPrefixInsertionIdentities.lean) | Exact ambient prefix deletion, fresh-vector and failure identities with the raw diagonal shift | Actual entries and finite dimensions retained |
| [SourceGreedyExposureConditions.lean](CircularLaw/SourceGreedyExposureConditions.lean), [GreedyPrefixRowConditional.lean](CircularLaw/GreedyPrefixRowConditional.lean), [GreedyPrefixColumnConditional.lean](CircularLaw/GreedyPrefixColumnConditional.lean) | Initial-positive progressive events supply every greedy insertion condition and both actual conditional failure bounds | Degree, raw-shift, fraction and height ranges explicit |
| [GreedyPrefixStepFailure.lean](CircularLaw/GreedyPrefixStepFailure.lean), [GreedyExposureHeight.lean](CircularLaw/GreedyExposureHeight.lean), [GreedyConditionalDrift.lean](CircularLaw/GreedyConditionalDrift.lean), [GreedyExposureCompletion.lean](CircularLaw/GreedyExposureCompletion.lean) | Actual acceptance/failure equivalence, height drift, terminal-rank failure and finite prefix-log upper probability | Initial-product probability vanishes by the exact normalization below; fixed-fraction asymptotics are proved below |
| [SquareRetainedPrefixIdentities.lean](CircularLaw/SquareRetainedPrefixIdentities.lean), [GreedyPrefixPaperNormalization.lean](CircularLaw/GreedyPrefixPaperNormalization.lean), [BernoulliGreedyCutoff.lean](CircularLaw/BernoulliGreedyCutoff.lean), [BernoulliGreedyPaperPrefix.lean](CircularLaw/BernoulliGreedyPaperPrefix.lean) | Exact normalized full/minor identities, literal rounded cutoff conditions, vanishing initial retained-zero probability and finite actual manuscript upper bound | Fixed-fraction asymptotic upper estimate is proved below |
| [BernoulliGreedyErrorRates.lean](CircularLaw/BernoulliGreedyErrorRates.lean), [BernoulliGreedyAsymptoticParameters.lean](CircularLaw/BernoulliGreedyAsymptoticParameters.lean), [BernoulliGreedyMinorUpperLimit.lean](CircularLaw/BernoulliGreedyMinorUpperLimit.lean) | All eventual finite-estimate conditions, fixed-fraction upper probability bound and actual full Bernoulli logarithmic convergence | Every fixed nonzero shift; degree tends to infinity and d/n tends to zero |
| [BernoulliHermitizationTheorem.lean](CircularLaw/BernoulliHermitizationTheorem.lean), [BernoulliBottomLogTailTheorem.lean](CircularLaw/BernoulliBottomLogTailTheorem.lean), [BernoulliCircularLaw.lean](CircularLaw/BernoulliCircularLaw.lean) | All three manuscript interface assertions, infinite-at-zero bottom tail and sparse Bernoulli bounded-Lipschitz circular law | Full named proposition and corollary proved; row-slice main theorem remains open |
| [BernoulliMinorUpperReduction.lean](CircularLaw/BernoulliMinorUpperReduction.lean) | Actual full Bernoulli logarithmic convergence follows from the fixed-fraction full-to-minor upper estimate with a vanishing deterministic error | Conditional reduction; the displayed upper probability estimate and part (ii) are proved below |
| [ScalarSquareSingularValues.lean](CircularLaw/ScalarSquareSingularValues.lean), [BernoulliEmptyMatrix.lean](CircularLaw/BernoulliEmptyMatrix.lean), [RoundedMinorLogReview.lean](CircularLaw/RoundedMinorLogReview.lean) | Actual scalar-identity singular values and positive-probability all-zero Bernoulli sample; source floors and ceiling checked at `n=100`, `epsilon=1/10`; exact upper logarithmic comparison fails there | Verified statement-review issue for `eq:SSS-T-upper`; [review note](HERMITIZATION_REVIEW.md), with no manuscript edits |
| [SourceFamilyProbability.lean](CircularLaw/SourceFamilyProbability.lean) | Whole-family K1, K2 and clustered-Pv probability sums for actual restricted canonical approximations; source energy inputs discharged, original separation hypotheses retained, uniform degree-band threshold | Supporting estimates for `thm:row-slice-structural` |
| [DegreeRates.lean](CircularLaw/DegreeRates.lean) | In the lower degree regime, `d/n` and `d^2/n` tend to zero; conditioning has logarithmic cost `o(n)` for `K<=n`; a logarithmic lower constant of at least 96 fits the proved max-weight diameter requirement | Section 3, conditioning cost and weight range; final regime split |
| [FiniteMean.lean](CircularLaw/FiniteMean.lean) | Uniform finite expectations; linearity, order, reindexing, Fubini, and independent product factorization | With-replacement model in Section 3 |
| [MaxWeight.lean](CircularLaw/MaxWeight.lean) | Pair-maximum identity, second-moment control, exponential bound, and max-weight theorem for the finite coordinate law, including odd sample sizes | Section 3, `lem:max-weight` |
| [MeasureMaxWeight.lean](CircularLaw/MeasureMaxWeight.lean) | Full max-weight lemma for arbitrary real probability laws with finite support diameter; integrability, measure-preserving sample regrouping, and passage to the conull support are proved | Section 3, `lem:max-weight` |
| [Tensorization.lean](CircularLaw/Tensorization.lean) | Quadratic small-ball bounds imply an exponential moment bound; independence gives the source tensorization estimate with constant `4*exp(1)`, arbitrary deterministic shifts, and radius zero | LLTTY19 Lemma 2.7; approved corrected manuscript `lem:tensorization` |
| [DoubleCounting.lean](CircularLaw/DoubleCounting.lean) | Deletion/extension incidence bijection; incidence and occupancy bounds; coordinate anti-clustering controls extension fibers; adjacent binomial ratio; small-ball probability bound with the low-occupancy probability explicit | Section 6, `lem:slice-double-count` |
| [Hypergeometric.lean](CircularLaw/Hypergeometric.lean) | Counts slices containing a fixed subset, proves factorial-moment and exponential lower-tail bounds, and completes the full slice anti-concentration lemma, including its supremum over centers | Section 6, `lem:slice-double-count` |
| [Assembly.lean](CircularLaw/Assembly.lean) | Convergence on complementary degree regimes implies convergence of the original sequence, including when one regime occurs only finitely often | Final argument in Section 9 |
| [Statement.lean](CircularLaw/Statement.lean) | Normalized empirical spectral measure with algebraic multiplicities; uniform area law on the disk; both measures have mass one in positive dimension; degree hypotheses eventually ensure `0 < d < n`; conditional assembly of the actual ESD tail probabilities | Sections 1 and 9 |

The full weight-entropy lemma is checked as a closed proposition:

```lean
example : CircularLaw.WeightEntropyLemma := CircularLaw.weight_entropy_lemma
```

Entropy is the nonnegative extended sum of `-p_j*log(p_j)`, with zero-mass
terms equal to zero. Dispersion is identified with the nonnegative integral
of the absolute difference of two independent copies. Finite dispersion
implies finite, summable entropy and gives the ordinary real inequality;
infinite dispersion gives an infinite right-hand side. The proof compares
finite partial entropy sums with exponential lattice weights and averages
over an independent center. It proves the bound for every integer law and
every measurable integer random variable on an arbitrary probability space.
The uniform-coordinate and actual dyadic-profile laws use the same pair
dispersion as the checked averaged-profile estimate. Their entropy penalty
absorbs `exp(-c*K*D)` when `K>=n/2`. `MultinomialEntropy.lean` proves the
factorial entropy bound directly from the weighted multinomial theorem,
with zero-sized bins allowed. `IntegerHistogram.lean` proves the actual
counts and identifies the exponent as dimension times the uniform-law
entropy. `DyadicHistogramEntropy.lean` identifies the floor labels with
the exact source intervals `[2^b,2^(b+1))` and proves the factorial entropy
bound and cancellation for those actual bin sizes. `ProfileFactorialEntropy.lean`
proves their sums of part sizes and exact factorial product regrouping,
then the global part-to-bin comparison, entropy inequality and cancellation
from the local compression estimate in each bin. `ProfileLogGeometry.lean`
proves that the exact truncated weights split each bin into four families
with exponential size decay. `FourFamilyEntropy.lean` and
`ProfileBinCompression.lean` give local factorial compression with constant
`4096`. `ProfileSmallBinMass.lean` gives total size at most `512*T` for any
subset of parts smaller than `T` in one bin. `CanonicalBinCompression.lean`
supplies the geometry from the constructed canonical partition and proves
both estimates for its actual parts, including their coordinate union and
the cutoff `T=d^(-kappa)*n`. Its entropy and dispersion-cancellation
consequences require no additional compression hypothesis. The actual
coordinate-multiset class-size formula is now proved in
`CanonicalClassCardinality.lean`, using an injective canonical part/value
encoding and exact fixed-size assignment counts. It also applies to every
restricted canonical approximation family. `CanonicalClassEntropy.lean`
combines this bound with dispersion cancellation; the actual inverse
truncated weights leave precisely the source height/weight product. The
four-block count in `UniformGradualClassCount.lean` now proves at most
`exp(n)` coordinate-multiset classes for the actual canonical approximation
family and every restricted subfamily. Their finiteness is proved. One
threshold is uniform over the standing logarithmic lower band, both
admissible codimensions, and every scale in the source range, with
`0<a3<=1/65536`. The original-coordinate block radii are `1`, `d^(3/2)`,
`d^3`, and `n^6`; exact finite grid counts and stars and bars precede the
checked entropy absorption. The logarithmic lower bound controls the
initial block's `n^6` alphabet cost. This supplies the manuscript's
class-count conclusion directly, without claiming the broader degree
scope of external Lemma 5.1. The K1/K2 branches and clustered-Pv
conclusion are proved below and assembled into the full named package.

The refinement development now proves exact floor composition at successive
scales, including negative coordinates, and the nesting of their actual
value levels. `LevelSliceCounts.lean` proves the exact survival threshold
and selected-prefix counts. `LevelRefinement.lean` identifies the unique
majority finer level outside the shrinking set and transfers prefix mass
with factor eight. `FloorGridCover.lean` proves that an injective coarse-cell
family has at most nine values in a disk of radius `1/k`; this bounds the
height of the actual greedy spread selection. The actual coordinate-mass
inequality in `RefinementMassDichotomy.lean` is
`high_combined_coarse_mass <= 288*fine_spread_mass + 41*shrinking_count`.
`SeparatedOrderDichotomy.lean` checks the source high-height/spread alternative
from two separated coordinate cohorts, and combines it with refinement.
If both consecutive spread masses are below `n3/4608`, at least `n3/656`
coordinates shrink by a factor two. `PlanarQuantileCohorts.lean` now
constructs the two cohorts from the gradual nonconcentration condition,
retaining the source scale `k>=5/theta0` and all rounded counts.
`GradualRefinementDichotomy.lean` supplies them from the exact normalized
source gradual class. `SourceRefinementFamilies.lean` defines the literal
spread and high-height families, including the original exponentially
growing height threshold. `AccumulatedShrinkage.lean` and
`GradualLevelAccumulation.lean` prove that avoiding the spread families
forces many final levels to have exponentially small coordinate counts.
`LowHeightCoordinates.lean` proves that these coordinates force actual
high-height mass. `GradualDecomposition.lean` closes the exact union
`S = union(4<=u<=v) Ku union Pv`, with `cK=1/4608` and `cP=1/65536`.
One dimension threshold works for every `v>=5`, every codimension parameter,
and every degree above `C*log(n)`, for fixed `0<a3<=1/2` and `C>0`.
This closes part (i) in the standing manuscript setting. The external
Lemma 5.9 constant `192` is not claimed; the weaker shrinking threshold
`n3/656` is fully absorbed by the proved positive decomposition constants.
The K1/K2 branches are now checked in `SourceK1Product.lean` and
`SourceK2Separation.lean`. `ProfileCutoffProduct.lean` proves the source
three-family calculation for the exact truncated weights and identifies
the original product of heights times inverse weights with the ratio
product. Actual spread coordinate mass equals the ordered profile spread
mass. If K1 holds and `a3*n>=4`, the floor-corrected product bound is
`d^(-(cK*a3/32)*n)`, and the actual class entropy consequence follows.
`IntegerOrderQuantiles.lean` retains ties and integer rounding in the
coordinate quantiles. `ProfileK2Separation.lean` supplies the actual
small-part bin bound `512*d^(-kappa)*n`. K2 then gives both probability
tails at least `cK*a3/32` and a gap at least
`(cK*a3/16384)*d^kappa`, where `kappa=cK*a3/16<1/3`.
A single dimension threshold works for every degree above `C*log(n)`,
every scale, and every codimension. The combined conclusion uses the
common positive constant `c1=cK*a3/16384`, with `C=1` in the product
estimate. This closes part (iv) in the standing manuscript setting.
The clustered-Pv conclusion is now checked in `SourcePvSeparation.lean`.
`ClosedFloorCells.lean` handles the closed-disk boundary and extracts a
repeated rounded value of mass at least `delta*n/9`.
`LargeSelectedLevel.lean` selects the last nonempty level chunk, with at
least one quarter of that mass. `RepeatedValueWeight.lean` bounds its
actual truncated weight by `72*sqrt(d)/delta`, giving the exact low tail
`delta/36` at the floor of that logarithm.
For the upper tail, write `s=cP*a3` and let `H` be the literal source
height threshold. `ProfileHighHeightBins.lean` and `SqrtHeightCutoff.lean`
use the actual canonical small-bin estimate at the stronger cutoff
`H/(d*sqrt(s))`. High-height coordinates below it have total mass at most
`512*(2-log_2(s)/2)*d^(-1/3)*n`. This is at most `s*n/4` once the degree
is large, independently of `v` and `H`. `SourcePvHighTail.lean` therefore
gives upper-tail mass `s/4`. The logarithm of this cutoff and exact integer
floors prove the required gap `s*(v-4)/2` under the original manuscript
separation hypothesis. No source statement is changed or strengthened.
One dimension threshold works for every degree above `C*log(n)`, every
`v>=5` and every codimension.
`SourceLLTTYPackage.lean` now assembles all five parts with the common
constants `cK=1/4608`, `cP=1/65536`, `c0=cP*a3/4`,
`c1=cK*a3/16384`, and `C=4096`, uniformly for `0<a3<=1/65536`.
Its full named target retains both admissible codimensions, the displayed
class-count scale conditions and the original clustered-Pv hypotheses.
The class-size and local-bin fields are checked for arbitrary actual
canonical reference vectors, so they include every manuscript class.
All constants precede the degree band, dimension, codimension, scales,
classes and vectors. This completes `prop:LLTTY-package`.

The Section 5 fixed-vector bound is checked for the literal radius
`R*log(d)*sqrt(d*n)/k`, for every `R>=1` and every actual `k`-vector.
`FixedNetSlice.lean` derives the canonical weight range and all finite
tensorization conditions uniformly in the degree band. `FullMatrixFixedNet.lean`
transports this estimate to the original full matrix law by exact restriction
and Euclidean reindexing. It includes every deterministic retained set and
vector shift; the empty retained set has the trivial bound one.

`ProfileMeanPowers.lean` proves the exact identity for the dimension power
of the geometric mean and its retained-row version at `K=n-L`.
The missing rows cost at most `(n*sqrt(d))^L`. `TailDispersion.lean`
turns two separated probability tails into `2*p*q*gap` pair dispersion.
For the actual K2 and clustered-Pv source branches, this gives the
degree-power and `delta*(v-4)` lower bounds respectively.
`ClassRowEnergy.lean` and `SourceClassRowEnergy.lean` combine these with
the checked class cardinality, entropy cancellation and K1 product decay.
Their uniform statements use the actual canonical approximations and
both source codimensions, with `K=n-L` and its row-count conditions proved.
These class estimates concern cardinality times the row weight/dispersion
factor. They now supply the probability sums described below.

`CanonicalClassStatistics.lean` proves that the actual weights and masses
agree under the bijection of nonempty creation-order labels. This gives
equal geometric means, pair dispersions and fixed-vector estimates on a
coordinate-multiset class. The leftmost-occurrence procedure can assign
individual repeated coordinates to different parts after a permutation;
the proof uses part data and masses. `CanonicalClassProbability.lean`
therefore bounds actual class probability sums and their event union,
allowing a different deterministic vector shift for every class member.
`FixedNetSplit.lean` and `CanonicalClassSplit.lean` separate the two
probability terms and insert the checked branch energies at `K=n-L`.

`CoordinateClassSummation.lean` constructs a fiber equivalence between
the original finite family and its represented classes. This proves exact
regrouping and that the class cardinalities sum to the family cardinality.
`CanonicalFamilyProbability.lean` applies it to the actual probability sum:
the dispersion term costs the number of classes, at most `exp(n)` in the
standing gradual setting, while the exception term costs the number of
net vectors. `SourceFamilyProbability.lean` discharges the energy inputs
for each actual K1, K2 and clustered-Pv restricted approximation family.
It keeps the class-count scale range, both codimensions, the original
cluster separation hypotheses and every conditioning and missing-row cost.
Cluster centers may vary between vectors. The final statements are uniform
over the degree band and all deterministic shifts.
`TwoAlphabetCounting.lean` encodes the actual top-coordinate set and the
two coordinate alphabets. `GradualNetCounting.lean` gives the exact crude
count `choose(n,n2)*A.card^n2*B.card^(n-n2)` for gradual approximations.
`GradualNetEntropy.lean` absorbs the top-coordinate logarithm using
`n2<=n/d^(2/3)` and the standing logarithmic lower degree bound. With
`C>=96` and `log(k)<=2*d^(1/96)`, it proves cardinality at most
`exp(128*n*d^(1/3))` for every restricted gradual approximation family.

`StructuralParameters.lean` retains the literal growth `(n/L)^(1/288)`,
radius, cluster fraction and floored terminal exponent. It supplies the
discretization logarithm budget at every exponent up to `vL` and proves
`rhoL<=d^(-vL)`. `StructuralDiscretization.lean` proves the required
`d^u<=sqrt(n)/d^(3/2)` range uniformly when `sigma<=1`, including the
manuscript's `0<sigma<1` setting. `StructuralNetUnion.lean` proves the
actual union count `vL*exp(128*n*d^(1/3))`.

`ProfileExceptionCost.lean` bounds the actual conditioning and row factors
and absorbs the crude net entropy. `ProfileExceptionUnion.lean` sums over
every `4<=u<=vL`; even after multiplication by the displayed `2*d^2`
prefactor, the profile-exception contribution is at most
`exp(-(averagedProfileRate/8)*n*d^(2/3))`. The radius constant is fixed
before this uniform dimension threshold. `SourceTerminalProbability.lean`
inserts the checked scale range and absorbed exception into the actual
K1 and K2 whole-family probability sums. Their remaining energy and
missing-row costs are absorbed by the following modules.

`MissingRowCost.lean` derives `(n*sqrt(d))^L<=exp(n)` from the actual
codimension and logarithmic lower degree bound. `LogarithmicNetCost.lean`
preserves the row factor's `log(d)^2` dependence, which gives a
`2*n*log(log(d))` exponent. `StructuralBranchEnergy.lean` absorbs all
fixed-scale costs into the checked K1 logarithmic and K2 degree-power
decay rates.
`FiniteProbabilitySupremum.lean` proves that a finite sample space has
only finitely many event probabilities, so each deterministic-shift
supremum is attained. One shift assignment attains every maximum in a
finite vector family. This converts the previous uniform shift bounds
into the manuscript's actual sum of fixed-vector suprema.
`SourceSpreadProbability.lean` proves that the actual K1/K2 mass cases
cover the full spread family and handles overlap of their approximations.
`SourceSpreadScaleSum.lean` closes the complete spread-family sum over
`4<=u<=vL` at rate
`exp(-(sourceK1DecayExponent(a3)/4)*n*log(d))`, including the displayed
`2*d^2` prefactor. Its threshold is uniform over the degree band, both
codimensions and every retained set, for fixed `a3` and radius constant.

`TerminalClusterParameters.lean` keeps the actual floor loss and proves
`deltaL*(vL-4)>=d^(1/192)/(4*log(d))`. The degree budgets in
`TerminalClusterBudgets.lean` absorb fixed logarithmic costs into this
quantity, uniformly over the standing degree band and both codimensions.
`TerminalPvHypotheses.lean` discharges every source separation hypothesis
at the literal terminal radius and cluster fraction.
`TerminalPvEnergy.lean` absorbs the class, missing-row and conditioning
costs into a positive multiple of `n*deltaL*vL`.
`TerminalPvProbability.lean` defines the actual terminal family with the
strict source cluster inequality, allows a vector-dependent centre, and
bounds its full sum of shift suprema. `TerminalPvPrefactor.lean` closes
the same sum after the displayed `2*d^2` scalar-grid cost, at rate
`exp(-(sourcePvDecayRate(a3)/4)*n*deltaL*vL)` plus
`exp(-(averagedProfileRate/8)*n*d^(2/3))`.

`CenteredCanonicalApproximation.lean` constructs the literal mean of the
canonical floor errors and the zero-sum centered error. Both mean
components lie in `[0,1/k)`, and the Euclidean error is at most
`2*sqrt(2)*sqrt(n)/k`. `ScalarMeanGrid.lean` rounds the mean at resolution
`1/(k*d)` and proves that its actual finite grid has at most `d^2` values.
`CenteredSliceAction.lean` proves the exact source shifted-kernel identity
and the zero-sum action bound under the actual retained centered-norm
event. `CanonicalNetKernelCover.lean` covers every continuous kernel
vector by its actual canonical image and mean-grid scalar. The fixed
spectral window is absorbed into the source logarithmic radius uniformly.
`CanonicalKernelProbabilityReduction.lean` checks the resulting probability
inequality with the actual sum of shift suprema. Its `d^2` prefactor is
stronger than the displayed `2*d^2`; the actual norm failure probability
remains explicit.
`TerminalKernelProbability.lean` combines all spread scales on the shared
norm event and charges its failure only once. It also converts the actual
clustered terminal sum into a continuous-vector kernel probability bound.
Both have their checked source decays plus that explicit norm failure term.

`SourceNormalCoordinates.lean` applies the weighted no-jump chain at the
literal starting rank and proves that every later valid rank of a
normalized gradual vector has modulus at most `d^16`. The floor normal
rank is positive and valid uniformly for both codimensions and fixed
`a` in `(0,1]`. `StructuralNormalRadius.lean` absorbs this polynomial
envelope into the actual structural growth and proves `eq:radius-comparison`.
It also rescales arbitrary cluster centres and preserves the strict
forbidden cluster count. This proof does not claim the manuscript's
intermediate `d^3*(n/qL)^6` inequality.
`StructuralKernelAlternatives.lean` derives the exact two structural
alternatives from the actual kernel compatibility and terminal-family
exclusions. Its uniform failure bound is `4/n` plus the three checked
exponential terms and twice the actual retained centered-norm failure.

`StructuralFailureBudgets.lean` now absorbs all three terminal decays
uniformly into `n^-2`. The actual structural failure is at most
`4/n+3/n^2` plus twice the retained centered-norm failure. If that norm
failure is at most `n^-100`, the exact two alternatives hold with
probability at least `1-5/n`. The norm tail is an explicit premise of
this conditional result. `RestrictedNormRetained.lean` now proves that
actual tail. `RestrictedNormUniform.lean` specializes it uniformly in the
source degree band. `StructuralKernelTheorem.lean` chooses admissible
fixed parameters and assembles the closed structural target.
`RetainedRowOrthogonality.lean` proves that membership in the orthogonal
complement of the actual conjugated-row span is equivalent to the literal
shifted matrix kernel condition, so the result applies to the manuscript's
subspace with probability at least `1-5/n`.

The restricted-norm concentration proof is checked:
`WeightedSliceLaplace.lean` expands the actual weighted slice generating
function over subsets and bounds it by the Bernoulli product. The exact
complement-slice equivalence treats negative tilts with the same product.
The mean is the actual `d/n` weighted sum. `WeightedMatrixLaplace.lean`
factors the independent row moments and supplies the squared-weight
variance proxy. `WeightedMatrixConcentration.lean` proves the two-sided
tail by finite Markov and bounded-tilt optimization.
`SignedMatrixConcentration.lean` separates positive and negative weights,
bounds both variance proxies by the original one, and gives the signed
tail `4*exp(-t^2/(16*v+8*K*t))`. Its deterministic inputs are an upper
bound `v` for `d/n` times the sum of squared weights and the absolute
coordinate cap `K`.

`LightCoupleBounds.lean` and `LightCoupleConcentration.lean` apply this
bound to the actual rank-one light coefficients at cap `sqrt(N)/n`.
For unit vectors with zero coordinate sum on the column side,
`N>=d`, `N>0` and `B>=1`, the raw light sum exceeds
`d/sqrt(N)+B*sqrt(N)` with probability at most `4*exp(-B*n/32)`.
The clipping error gives the mean bound, and the squared coefficients
give the variance bound.
`RowSliceEdgeCounts.lean` identifies actual rectangular edge counts with
support intersections and proves their exact mean and exponential moments.
`RowSliceEdgeTails.lean` optimizes those moments to prove the Poisson
upper tail. For fixed nonempty row and column sets, the event
`exp(2)*mu<E` and `c<E*log(E/mu)` has probability at most `exp(-c/2)`.
Its threshold comes from a minimum over the actual finite bad sample set.

`EdgeDiscrepancyEntropy.lean`, `RowSliceDiscrepancy.lean` and
`RowSliceDiscrepancyUnion.lean` now prove simultaneous discrepancy.
The actual binomial set counts are absorbed into the fixed-set tail,
then all possible nonempty set sizes are covered. For `m<=n`, positive
degree `d<=n` and `beta>=0`, the source discrepancy alternatives with
parameters `exp(2)` and `2*(beta+4)` have probability at least `1-n^-beta`.
This checks the discrepancy input of LLY26a Lemma 4.7.
`RowSliceColumnBounds.lean` proves that every column load is at most
`9*d` except with probability at most `n*exp(-9*d)`.
`MatrixDiscrepancy.lean` defines the literal matrix conditions, and
`RowSliceMatrixDiscrepancy.lean` identifies them with the checked support
events, including the actual row sums and column loads. Nonnegativity
and row/column bounds also give both deterministic edge-count bounds.
`RowSliceNormEvents.lean` combines these actual matrix conditions:
for `0<m<=n`, `n>=2`, positive degree `d<=n`, `A>=0` and
`(A+2)*log(n)<=9*d`, the joint event with discrepancy parameter
`2*(A+5)` and row/column bound `9*d` has failure at most `n^-A`.

`NormDyadicLevels.lean` constructs a complete partition from the least
power of two bounding `sqrt(n)*abs(x_i)`. Its base level includes small
and zero coordinates. `NormDyadicMass.lean` proves exact regrouping and
total level mass at most five for vectors of squared mass at most one
and at most `n` coordinates. `NormHeavyDyadicCover.lean` bounds the
actual heavy bilinear sum by the finite sum of scaled edge counts across
these levels. Every heavy pair forces its level product above the
threshold, and every coordinate pair is covered by the exact fibers.

`NormDyadicSums.lean` proves increasing and reciprocal geometric
budgets on arbitrary finite level sets. `NormHeavyLevelRatios.lean`
identifies their normalized costs with the actual matrix edge counts.
`NormHeavyDegreeSums.lean` checks the small-scaled-ratio and degree
branches. `NormHeavyEntropy.lean` derives the actual discrepancy
logarithm inequality for the larger coordinate fiber.
`NormHeavyLargeRatio.lean`, `NormHeavyModerateMass.lean` and
`NormHeavySmallMass.lean` check the other three branches.
`NormHeavyCaseAssembly.lean` proves that all five cover every oriented
heavy pair and bounds their actual sum by
`25*cap+10/C+40*kappa2/C+80*kappa2/(C*cap*log(cap))+10`.
`NormHeavySquare.lean` checks the literal transpose's discrepancy and
degree conditions, covers both fiber-size orderings, and proves the
full square heavy bilinear bound with this budget times `2*C*sqrt(N)`.
The constant is independent of dimension. It is our own checked
constant for the complete base-zero partition, rather than a claim
of the original numerical constant in LLY26a Lemma 4.8.

`NormRectangularPadding.lean` and `NormPaddingDiscrepancy.lean` prove
that literal zero-row padding preserves every required matrix condition.
`NormHeavyRectangular.lean` transfers the square bound without changing
its constant. `RowSliceHeavyBound.lean` applies it to the actual row-slice
degree/discrepancy event with `N=9*d` and `C=1/9`.

`NormLatticeCardinality.lean` counts the literal bounded integer vectors
by the checked Gaussian lattice sum. `NormLatticeRounding.lean` constructs
an approximation inside the unit ball, and `NormLatticeNet.lean` gives
an actual quarter-net of cardinality at most `128^n`.
`NormMeanProjection.lean` proves the exact finite variance identity,
norm contraction and the zero-sum projected net. `RowSliceLightNet.lean`
charges the actual net-pair cardinality and gives failure at most
`n^(-(A+1))` with `B=32*(A+20)`.

`NormFiniteNetReduction.lean` extends net-pair control to the continuous
real Euclidean operator, with a sufficient factor two. `RowSliceRealNorm.lean`
combines the light and heavy failures under `(A+3)*log(n)<=9*d`.
`NormRealComplexTransfer.lean` checks real/imaginary projections and the
literal complex action. `RestrictedNormTheorem.lean` proves the full named
proposition: for every fixed `A>0`, one positive finite constant `C_A`
supplies both the threshold `d>=C_A*log(n)` and norm bound `C_A*sqrt(d)`,
with probability at least `1-n^-A`, in the source ranges. It also checks
the actual full-law entry mean and the complex centered-row identity.
`RestrictedNormRetained.lean` supplies the actual retained `n^-100` tail
for every deterministic retained set under `103*log(n)<=9*d`.
`NetReductionTheorem.lean` now supplies the full named net-reduction lemma,
including finite canonical images, exact profile class cardinalities,
class counts, kernel probability reduction, and the crude union count,
uniformly for every subfamily of the actual gradual family. Both
`lem:net-reduction` and `thm:row-slice-structural` are counted as proved.

The Gaussian normal argument now has its actual probability model.
`StandardComplexGaussian.lean` constructs the image of two independent
real Gaussians of variance one half. `ComplexGaussianLinearForm.lean`
proves the exact laws of every real linear form, its characteristic
function, and complex norm second moment one. `ProjectedComplexGaussian.lean`
constructs the independent coordinate product and the continuous projection
onto the actual deterministic orthogonal complement, with Gaussian law and
the retained shifted kernel condition. `GaussianInnerLaw.lean` proves that
every Hermitian form has the law of its coefficient norm times a standard
complex Gaussian. Thus each projected coordinate difference has scale
`norm(P_Eperp(e_i-e_j))`, including degenerate directions.
`ComplexGaussianDensity.lean` proves the exact density
`exp(-norm(z)^2)/pi`. `ProjectedGaussianSmallBall.lean` gives the
arbitrary-centre disk bound `(r/scale)^2` for every positive projected
difference scale. `ComplexGaussianRadialTail.lean` now derives the exact
tail by polar integration and proves that radius equality has measure zero.
`GaussianCorrelationSmallBall.lean` defines strong correlation by the actual
projected tail and proves the source fixed-pair bound, including degenerate
projection handling. `ClusterPairCounting.lean` and
`GaussianClusterAveraging.lean` check the source averaging bound at radius
`alpha*s/sqrt(16*log(1/beta))`: if every retained index has at most `b`
correlated neighbours, disk-count failure is at most `(s*n)^2/(2*b^2)`.
The proof integrates the count of close non-correlated ordered pairs;
it assumes no independence between projected coordinates.
`GreedyCorrelationClusters.lean` now constructs the literal maximal star
clusters with cardinality-first lexicographic indicator-vector order. Their
sizes decrease, they are pairwise disjoint, and the remaining set is empty
after at most `n` stages. The first cluster of size at most `b` defines the
exceptional set as the union of all earlier clusters. Lean checks its exact
cardinality sum, the bound `stop*(b+1)<=n`, representative indices, and at most
`b` correlated neighbours per remaining index. `GaussianGreedyClusters.lean`
checks reflexivity, symmetry and the additive correlation bound, hence
`(2*alpha,2*beta)` correlation inside each actual star. It applies the
averaging estimate to the constructed exceptional set without a remaining
neighbour-count hypothesis. `CoordinateDiskEvents.lean` proves that the
disk-count failure event is closed and measurable by anchoring each possible
nonempty coordinate subset in a fixed compact ball. Taking its complement
gives the corresponding success probability; smaller radii and `2*b<=L`
give the source disk-cardinality conclusion.
`GaussianSourceParameters.lean` checks the literal manuscript choices:
`b=floor(L/2)`, `s=(L/n)^(3/2)/2`, and `beta=(L/(4*n))^3/4`.
For `L>=2`, floor arithmetic bounds the failure by `9L/(8n)`.
The bound `log(q)<=288*q^(1/288)` and explicit logarithmic estimates prove
that increasing the correlation exponent constant by 1024 absorbs all
radius factors, uniformly for `q=n/L>=1`. `GaussianSourceAntiClustering.lean`
defines the literal exceptional set at these parameters and the full
measurable source event, and proves its probability conclusion once that
set has size at most `2*n*(L/n)^(1/576)`. A single constant `C_G+1024`
controls the source radius and failure bound for `C_G>=0`.
`GaussianRepresentativeCombination.lean` supplies unit coefficients for
`p+1` vectors whose combination has equal values at all `p+1` prescribed
representatives: the `p` difference constraints have a nonzero kernel.
Normalization is checked, and combinations of actual projected Gaussian
copies remain in the original orthogonal complement. Uniform non-flatness
below proves that the unit combination is nonzero, and the final coordinate
comparisons give the required ordered-coordinate bounds.
`GreedyCorrelationOwners.lean` supplies the unique earlier star for each
exceptional coordinate and the actual representative lookup. The lookup is
correlated to that coordinate and takes a common value whenever all star
representatives do. `ProjectedGaussianCopies.lean` constructs the literal
product law of `p` independent samples; the projected copies have exact
marginals and pair-tail probabilities and are jointly Gaussian.
`CopyClusterCounting.lean` counts coordinates which are far from their
representative in any copy. The union bound gives expected count at most
`p*beta*card(J)`; integration and Markov give failure at most `2*p*beta`
for half the coordinates to be far. The count and complementary success
event are measurable. `GaussianCombinationClusters.lean` transfers closeness
to any coefficient vector of Euclidean norm at most one, without making a
measurable coefficient choice. Equal representative values then yield a
closed disk of radius `p*alpha` containing more than half of `J`.
`GaussianGreedyCopyClusters.lean` applies both steps to the actual greedy
exceptional set and projected-copy law. The copy count satisfies
`p<=2*n/L`; at `beta=(L/(4*n))^3/4`, failure is at most `1/64` and the
measurable success event has probability at least `63/64`. On every success
sample the checked unit combination is orthogonal and has the stated large
coordinate cluster. Uniform non-flatness below excludes zero output; the
final comparisons give reverse steepness and the structural disk radius.
`GaussianCopiesCombinationLaw.lean` now proves the exact raw combination law
using nested product characteristic functions. Its scale is the Euclidean
coefficient norm, including zero coefficients; projection commutes with the
combination. Every fixed unit combination has the original projected law,
and probabilities agree for every measurable event. This distribution
identity alone gives no simultaneous lower bound over coefficient vectors.
`GaussianCoordinateTails.lean` proves the projected-coordinate law at scale
`norm(P_Eperp(e_i))<=1`, with tail at most `exp(-r^2)` even when that scale
vanishes. The same bound holds for fixed unit combinations. A finite
coefficient set S has coordinate-union failure at most
`card(S)*n*exp(-r^2)`. For all p actual copies the failure is at most
`p*n*exp(-r^2)`, with a measurable complementary event. Cauchy--Schwarz
transfers it to every coefficient vector of norm at most one, with coordinate
bound `sqrt(p)*r`. Setting `r=sqrt(log(p*n/epsilon))` gives probability at
least `1-epsilon` for `0<epsilon<p*n`. This checks a uniform bound for the
largest coordinate; it does not prove the sharper rank-dependent bounds in
Proposition 4.7. The non-flatness estimate is checked below.
`GaussianIsometryLaw.lean` now proves the exact standard Gaussian law under
the adjoint of every complex linear isometric embedding. It constructs the
literal coordinate map using the standard orthonormal basis of any
deterministic subspace F, identifies it with the embedding adjoint and proves
that its norm equals `norm(P_F G)`. The raw sample law maps to the actual
standard Euclidean Gaussian law in `finrank(F)` dimensions.
`ComplexGaussianNormLaplace.lean` derives the integrable exponential moment
`E exp(t*norm(G)^2)=(1-t)^(-r)` for every `t<1` from the planar density and
the actual coordinate product. Exponential Markov bounds both tails. For
`r>0` and `u>0`, the lower tail is at most `(exp(1)*u/r)^r`; the upper tail
at squared threshold u is at most `2^r*exp(-u/2)`.
`GaussianProjectionNorm.lean` transfers the squared-norm law and all these
bounds to the actual projection onto every deterministic subspace, including
the normal `P_Eperp G`. Its dimension is the subspace dimension.
`GaussianCoordinateDeletion.lean` constructs the actual normal subspace
vanishing on a coordinate set K. Rank-nullity proves that its dimension
is at least `finrank(Eperp)-card(K)`. Its projected norm is bounded by the
norm of the normal's remaining coordinates. The Gaussian norm estimate
therefore bounds the event that every coordinate outside K has norm at
most tau by `(exp(1)*n*tau^2/r)^r`, where r is the actual remaining
subspace dimension.
`GaussianOrderSmallBall.lean` now sums over the actual coordinate subsets.
For positive k below m, when the Gaussian base is at most one, its bound is
`choose(n,k)*(exp(1)*n*tau^2/(m-k))^(m-k)`. Checked binomial entropy gives
the one-vector non-flatness estimate with rank `floor(m/512)`, threshold
`m/(512*n)` and failure `exp(-m/512)`, for `m>=512`.
`OrderedNormContinuity.lean` proves that the actual ordered norm is
Lipschitz with constant one, including ties, so its sublevel events are
closed and measurable. `GaussianOrderCombinations.lean` transfers the
event law to each fixed unit combination and checks the finite-set union.
`ComplexSphereGrid.lean` constructs the actual finite unit sphere cover by
canonical rounding, removal of zero and normalization. Its cardinality is
at most `(2*k+3)^(2*p)` and its Euclidean cover radius is `4*p/k` for
`k>=8*p`. `GaussianNonflatNet.lean` checks measurability of the bad event
for some unit coefficient by compact projection, and passes the finite
bound to all unit coefficients at resolution `k=4096*p^2*n^2`.
`GaussianNonflatUniform.lean` absorbs the actual grid entropy and the
coordinate-tail error. Uniformly for all deterministic E and positive p,
at sufficiently large n, `sqrt(n)<=m<=finrank(Eperp)` and `p<=n^(1/4)`
give failure at most `exp(-m/2048)` for some unit combination to have
ordered norm at rank `floor(m/2048)` at most `m/(2048*n)`. The explicit
constant `1/2048` supplies the non-flatness content of Proposition 4.4.
On a measurable complementary event every unit combination has this
positive lower bound and is nonzero. No finite-net, Gaussian norm or
non-flatness estimate remains an assumed input to this result.
`GaussianSourceRange.lean` checks every finite prerequisite uniformly over
all d and L in the manuscript's full standing band and codimension interval:
`L>=sqrt(n)`, `p<=n^(1/4)`, `log(n)<=n/L`, arbitrarily large `n/L`, and
`0<qL<=floor(L/2048)` for every fixed `0<a<=1/2048`.
`GaussianForbiddenComparisons.lean` uses the uniform largest-coordinate
estimate at `epsilon=1/64`. In this range it is at most `(n/L)^2/4096`,
which, together with the ordered-coordinate lower bound, implies every
reverse-steepness inequality through qL. The same module absorbs `p*alpha`
into `exp(-2*(n/L)^(1/288))*L/(2048*n)` at correlation exponent 8192.
`GaussianExceptionalContradiction.lean` consequently rules out an oversized
actual exceptional set on every common success sample: its nonzero unit
combination is in Eperp, obeys all reverse inequalities, and has a disk
violating the structural bound.
`GaussianAntiClusteringTheorem.lean` proves that the three measurable success
events have a common sample, discharges the exceptional-size premise, and
assembles the full named fixed-subspace Gaussian proposition. The admissible
normal parameter is `a0=1/2048`, and the common final radius and failure
constant is 9216. The threshold is uniform in the deterministic subspace,
degree and codimension for fixed standing parameters. This statement uses
the lower-band and absolute-constant conventions in Section 2, which apply
throughout Section 6. The sharper general LLTTY21 Lemma 4.5/Proposition 4.7
remain unproved; the checked largest-coordinate argument suffices here, so
these broader estimates are not dependencies of the completed proposition.

`GaussianRowSpanExtension.lean` now implements the manuscript's literal
least-coordinate enlargement. It selects the least j with nonzero
`P_Fperp(e_j)`, normalizes that projection and adjoins its line. Each stage
below dimension n increases rank by exactly one. Iteration to the target
rank contains F and has exactly that rank, including deficient retained
row spans. The actual retained-row span has rank at most the retained
cardinality, so this enlargement always applies. The enlarged subspace
depends only on retained rows; its finite-sample measurability and the
joint measurability of its projected Gaussian normal are checked. Its
orthogonal complement lies in the actual retained shifted kernel, and
the exact structural alternatives pass to it. Projection norms decrease
under enlargement. The stronger structural interface allows every fixed
`0<a<=1`, with an absolute lower-degree constant independent of a, so the
normal parameter can be chosen in the Gaussian theorem's admissible range.
`FiniteDiskConcentration.lean` checks attainment and measurability of the
literal concentration supremum over all complex centers, including closed
disk boundaries. `GaussianFreshRowParameters.lean` places both source
codimensions in the Gaussian theorem's range and checks the exceptional
fraction, occupancy tail and radius comparisons with one uniform threshold.
`GaussianFreshRowSmallBall.lean` proves the full averaged fresh-row estimate
with the supremum inside the expectation. Structural failure contributes
at most `5/n`; Gaussian failure and the good-event concentration bound
give the `O(d^-3)` term. No probability estimate remains an assumed input
of that closed theorem.

`FreshRowGaussianProbability.lean` proves the omitted row's actual
small-ball bound on the matrix–Gaussian product law. Exact coordinate
resampling leaves the enlarged retained span unchanged; finite averaging
and Gaussian integration commute, and the diagonal shift only changes
the disk center. `GaussianRowDistance.lean` identifies the actual row
distance with its orthogonal projection norm. A projected Gaussian form
has that norm as its scale, so distance at most the radius gives small-ball
probability at least one half. The resulting per-index row-distance
probability is bounded by `R/d^3 + R/n` at radius
`exp(-R*d^(1/96))`, uniformly in the source band, codimensions, retained
sets and spectral window. No independence between distance events or
simultaneous structural event over retained sets is asserted. These
inputs are now assembled into the full intermediate theorem below.

`BadRowMarkov.lean` sums the per-index probabilities to bound the actual
bad-row expectation by `R*n/d^3+R`. Markov at the literal source threshold
`t=ceil(n/d^2)` gives `R/d+R*d^2/n`; the degree range reduces this to
`2*R/d`. No independence between bad-row events is used. `RowDeletion.lean`
selects an actual subset of exactly `N-t` surviving rows. Deleting rows
shrinks every comparison span, so the actual surviving distances remain
at least the radius. Positive distances prove linear independence and
full row rank. The corresponding uniform event has probability at least
`1-2*R/d`.

`RowDistanceDual.lean` constructs the normalized projected row residuals.
They lie in the actual row span, are biorthogonal to its conjugated rows
and have squared norm equal to the inverse squared row distance.
`RowGramInverse.lean` uses this biorthogonality to reconstruct every vector
in the span and identify the inverse row Gram matrix. Its diagonal and
real trace are exactly the inverse distance energies.
`HermitianInverseTrace.lean` proves the spectral inverse-trace formula by
unitary diagonalization and an explicit diagonal right inverse.
`RowNegativeSecondMoment.lean` checks that the actual row Gram is `H H*`,
defines singular values as its ordered eigenvalue square roots, and proves
their nonnegativity and decreasing order. Full row rank implies positive
leave-one-out distances. The negative second-moment identity is proved
for this actual retained shifted matrix, including the post-deletion bound
`sum_j s_j(H)^-2 <= k/r^2`. A closed uniform theorem supplies this bound on
a surviving submatrix with probability at least `1-2*R/d` throughout the
source band.

`SingularValueCounting.lean` checks that a decreasing positive list's tail
contributes at least `(k-j)/s_j^2` to the inverse second moment, where Lean's
index `j` starts at zero. The resulting bound is
`s_j >= r*sqrt((k-j)/k)` and gives `s_j >= r/d` whenever
`k <= (k-j)*d^2`. Both bounds apply to the actual surviving shifted matrix.
`SpectralRayleighBounds.lean` expands the quadratic form and norm in an
orthonormal eigenbasis and proves the head/tail bounds. Rank-nullity and
subspace intersection give the eigenvalue lower bound from a subspace of
dimension above `j`. `SpectralSubspaceComparison.lean` verifies the leading
eigenspace's exact dimension and transports it through a linear isometry.
`EuclideanCoordinateEmbedding.lean` constructs the coordinate isometry and
checks exact equality of principal quadratic forms.
`PrincipalEigenvalueComparison.lean` proves the principal Hermitian
eigenvalue bound. `RowSingularValueComparison.lean` identifies the actual
retained Gram as a principal submatrix and proves same-position singular
values increase when rows are added, including rank-deficient matrices.
`IntermediateIndexBounds.lean` checks the literal
`q0=floor(n/d^3)-1+2*ceil(n/d^2)` and proves `q0<=5*n/d^2<n` for
`d>=4` and `4*d^3<=n`, which hold uniformly in the lower band eventually.
The zero-based index `n-q0-1` is valid in the full and surviving matrices;
adding one gives the source position `n-q0`, and exactly `t+1` singular
values lie in its surviving tail. The degree-count condition for `r/d`
follows from the literal ceiling, without dropping its rounding.
`SquareSliceSingularValues.lean` defines the singular values of the full
literal shifted square matrix from its nonnegative `A A*` spectrum and
identifies the retained row Gram as a principal submatrix of that product.
`IntermediateExponentialRadius.lean` proves
`exp(-(R+1)*d^(1/96))<=exp(-R*d^(1/96))/d` once
`log(d)<=d^(1/96)`, uniformly over the lower band.
`IntermediateSingularValueTheorem.lean` combines these checked results on
the actual matrix law. It has one absolute positive lower logarithmic
constant, positive radius and failure constants, and a uniform dimension
threshold for every fixed spectral window, lower constant and sigma.
`FixedShiftIntermediateTheorem.lean` applies it to `z*sqrt(d)` and proves
the success probability tends to one for every fixed complex `z` and every
lower-band degree sequence. Thus both `thm:intermediate` and its introductory
restatement are proved. This increases the named-result count by two,
because the catalog includes both statements of the same mathematical
result. `IntermediateDeletionBudget.lean` proves
`q0*d*log(d)/n<=5*log(d)/d` and its limit zero, supplying the scalar
deletion-count budget in Section 9.

The all-ones eigenvector is proved nonzero for `n > 0`. The incidence argument
uses an explicit bijection `(S,t) ↔ (S.erase t,t)`; it is not replaced by an
assumed combinatorial identity.

The Section 4 witness bounds count supports and use their exact coordinate
laws before applying independence across rows. The unique-coordinate count
uses only rows outside the chosen coordinate sets, with the full matrix law
restricted to those rows exactly. The ordered-jump exclusion is simultaneous
over all vectors and constant shifts satisfying its deterministic inequalities.
The actual recursive shifted `T0` class is now excluded on the prescribed
multiscale event, with its `exp(-c*n/d^3)` failure bound. This uses the literal
floor stride, least starting exponent, final exponent and terminal ceiling,
and applies to both codimensions and all allowed spectral shifts simultaneously.
The `n1` witness failure also has its `exp(-c*n/sqrt(d))` bound. All finite
conditions are discharged throughout the source logarithmic degree band.
The permitted shifted `T3` inclusion into `VL` and the full deterministic
almost-constant reduction are now proved. The reduction keeps the literal
almost-constant coordinate count, radius `10/d^3`, `S(12)` and all four shifted
source classes, and treats both positive-tail and zero-tail vectors. The
thresholds for it and the `T0`/`T3` inputs are uniform over every degree in
the lower band. The row-load argument is now complete: the literal event
has failure probability at most `exp(-(rowLoadRate/4)*n)`, with a positive
absolute rate. The small-coordinate-set count uses the checked upper entropy
bound `t*(1-log(t))`, which tends to zero and supplies a fixed positive
admissible range for `a3`. The argument preserves the literal floor `n3`,
all four source coordinate sets and the `n/2` surviving-row count. A centered
support-sum estimate gives the exact `d/2` action lower bound, including the
diagonal term. The resulting kernel exclusion is simultaneous over all
almost-constant `S(12)` vectors and all shifts in the source window, with
one threshold uniform in the degree band and both codimensions. It is a
closed checked proposition:

```lean
example : CircularLaw.AlmostConstantRowLoadExclusionLemma :=
  CircularLaw.almost_constant_row_load_exclusion_lemma
```

The final gradual normalization is also proved. Sorted moduli scale by the
scalar norm without assuming that the sorting permutations coincide; this
gives homogeneity of the literal recursive steep classes and count-defined
almost-constant class. A zero third-scale modulus puts a vector in the
almost-constant class with center zero. Every vector outside that class and
the full steep union can therefore be divided by its positive third-scale
modulus to enter the exact source gradual class. The deterministic bridge
combines the almost-constant reduction, the load exclusion and the permitted
`T3` inclusion to give the source kernel alternative once the three excluded
steep classes have been ruled out. Its threshold is uniform over the degree
band and both codimensions. The `T1` and `T2` exclusions are explicit
inputs of that deterministic bridge, discharged by the full theorem below.
Actual finite three-range grid nets are now constructed
for the normalized literal classes, with exact integer grid and small-set
counts. The approximants have coordinate error `d^(-3/2)`, ordered modulus
above `2/3` at the normalization rank, and zero moduli at and beyond the
next rank. A separate constant grid approximates the permitted center.
The actual rectangular matrix error is at most
`2*(1+Z0)*sqrt(n/d)` in the source spectral window. Every shifted `T1/T2`
kernel vector can be normalized and mapped to these nets. Finite probability
bounds apply the checked equal-block estimates to each member, keeping the
witness failure outside the net union. The sharp
`exp(7*n_next*log(d))` net-size estimate is now proved for the actual product
of the two grids. The proof retains every literal floor and ceiling, bounds
the integer grid radii, and absorbs support entropy and both short prefixes
with coefficient seven. All finite thresholds hold uniformly over every
degree in the source lower band. The closed source steep-net lemma combines
this count with the geometry and component approximation for both
codimensions:

```lean
example : CircularLaw.SourceSteepNetLemma :=
  CircularLaw.source_steep_net_lemma
```

The remaining equal-block rank, fit and radius conditions are now discharged
uniformly. The literal T1 ceiling and T2 floor ranks retain the required
ordering and block fits. Both actual approximation radii fit the checked
equal-block small balls. For T1, `log(d)/d^(1/6)` tends to zero and absorbs
the net count into the `n/sqrt(d)` rate. For T2, the exact floor ratio has
logarithm at least `log(d)/6`; a proved fixed positive range for `a3` absorbs
the net count into an `n*log(d)` rate. The separate witness failures give
the source final rates `exp(-c*n/sqrt(d))` and `exp(-c*n)`.

The full named rectangular kernel compatibility theorem is now proved.
Failure of the exact very-steep-or-gradual-cone alternative is contained
in the three actual shifted-class kernel events or row-load failure.
All four checked exponents give the explicit failure bound `4/n`, with a
fixed absolute logarithmic lower constant independent of the degree-band
parameter and spectral window. The target proves a positive admissible
range for the fixed sufficiently small `a3`, and retains the literal
floor codimensions, exact source classes, nonzero complex scalar cone and
full row-slice matrix law. One threshold covers both codimensions, every
deterministic retained set and every shift in the prescribed window:

```lean
example : CircularLaw.RectangularKernelCompatibilityTheorem :=
  CircularLaw.rectangular_kernel_compatibility_theorem
```

The full coordinate-range lemma is now separately complete. Its maximum
bound comes from the recursive no-jump chain and the literal terminal
ceiling; the actual floor stride eventually satisfies `4*d <= p^3`.
The first-scale ceiling gives the finite coefficient bound needed for
`x*_1 <= n^6`. Outside the literal `T2` class, the normalized gradual vector
has `x*_{n2} <= d^(3/2)`. Canonical floor rounding gives both factor-2
bounds, for every positive integer `k` and every sorting permutation,
including arbitrary tie choices. All finite conditions are discharged
uniformly over every degree in the source lower band and both codimensions:

```lean
example : CircularLaw.CoordinateRangesLemma :=
  CircularLaw.coordinate_ranges_lemma
```

The Fourier development uses the source's `exp(-2*pi*i*inner(t,x))`
normalization. `BoundedDensityFourierPowerLemma` is a closed, proved
proposition for arbitrary integrable planar densities bounded by one almost
everywhere and having integral one. Its constant is `200`; the source's
numerical `47` is not claimed. The product estimate and almost-everywhere
inversion now prove the actual sum-density conclusion of LLTTY19 Proposition
2.4, with constant `200/m` for every `m>=1`. Radon--Nikodym supplies the density,
and independence supplies the joint product law when the summands are on an
arbitrary probability space. Neither correspondence is assumed. The closed
result is checked by

```lean
example : CircularLaw.IndependentPlanarDensityLemma :=
  CircularLaw.independent_planar_density_lemma
```

The discrete planar concentration import, Proposition 2.5, is now proved
with absolute constant `10000`:

```lean
example : CircularLaw.IndependentPlanarDiscreteLemma :=
  CircularLaw.independent_planar_discrete_lemma
```

Its hypotheses are actual marginal laws concentrated on `delta`-separated
points with atoms at most `u`, and independence on an arbitrary probability
space. It includes the source's iid case and permits radius zero. Uniform
disk noise has radius `delta/3`; the proved second-moment and Markov bound
replaces the source's Hoeffding step. The support need not be finite, and
no noise tail or sum-density assumption is added. `RegularBlock.lean`
applies this to actual finite uniform block samples with balanced levels
and `1/k` separation. It proves the regular branch's inverse-weight bound
with constant `40000`, including the precise radius `tau*sqrt(d)/k`
and weight `h*m/d`. The general planar Esseen import in Proposition 2.2 is
also proved. The Miroshnikov import in Proposition 2.3 and both spread-sum
branches are now proved, completing the conditional and averaged row results.

The Esseen proof checks the Gaussian Fourier identity, characteristic-function
factorization for the actual independent sum, symmetrized concentration deficits,
periodic cosine integration, volume-preserving rotations, and weighted Jensen
under the actual moment-tilted law. It first proves the stronger bound
`(24*exp(1)/pi)*(r/r0)/sqrt(sum(1-Q_i(r0)))`, then the source's squared-radius
form. The extended-real formulation treats a zero concentration deficit as an
infinite upper bound. No density, moment estimate, or general concentration theorem
is assumed. Its closed target is checked by

```lean
example : CircularLaw.IndependentPlanarEsseenLemma :=
  CircularLaw.independent_planar_esseen_lemma
example : CircularLaw.IndependentPlanarMiroshnikovLemma :=
  CircularLaw.independent_planar_miroshnikov_lemma
```

The canonical decomposition is now implemented from the actual vector.
The floor formula and lattice separation, leftmost-level recursion, and
its correspondence with the global remaining-coordinate algorithm are
proved. The spread scan uses the greatest lexicographic value which has
a separated partner, matching the source seed. Its selected values are
separated, number at least two when nonempty, and cover the unselected
values within the prescribed distance. The constructed parts have balanced
level counts and form a disjoint cover of the coordinates. Their heights
and sizes are invariant under permutation. The ordered profile puts all
spread parts first, then regular parts, with each kind in increasing order;
the number of nonempty parts is eventually at most `3*log(n)`.

`CanonicalRow.lean` consequently proves the regular bound for the actual
count-conditioned row, without assuming a partition, level balance, or
lattice separation. It also specializes the averaged estimator to the
constructed ordered profile. `CanonicalSpread.lean` checks both spread
single-summand inputs for these parts. The Miroshnikov spread-sum estimate
is now proved for arbitrary independent planar laws. Its proof uses the actual
translated-square concentration, the first integer half-mass scale, localized
convolution, the checked Esseen bound, and induction on the number of summands.
The final disk comparison preserves the exact `sqrt(2)*r` single-summand radius.

`ConditionalRow.lean` completes the count-conditioned row lemma at degree
at least `65536`, with no block estimate left as a hypothesis. The target
parametrizes every feasible count profile by a reference sample tuple, and
the checked count-fiber law supplies the conditional probability. Its visited
minimum is exactly the paper's `SB(Q)`. `AveragedRow.lean` proves both averaged
conclusions and every deterministic scalar translation. The finite mean of
the fiber-constant estimator is its expectation over `Q`; pairwise dyadic range
is the diameter of the finite coordinate-mass law, and the geometric mean is
`W_y`. Coincident dyadic bins aggregate their coordinate masses. An absolute
degree threshold absorbs the occupancy prefactor. `ProfileTensorization.lean`
also proves the corresponding matrix and row-slice bounds, using the Euclidean
norm and arbitrary deterministic vector shifts.

The four complete named results are checked as closed propositions:

```lean
example : CircularLaw.MaxWeightLemma := CircularLaw.max_weight_lemma
example : CircularLaw.SliceDoubleCountLemma := CircularLaw.slice_double_count_lemma
example : CircularLaw.ConditionalRowSmallBallLemma := CircularLaw.conditional_row_small_ball_lemma
example : CircularLaw.AveragedRowProfileLemma := CircularLaw.averaged_row_profile_lemma
```

The max-weight constants are `epsilon0 = 1/12` and `c = log(2)/4`.
The statement uses the actual power-of-two expression from the paper,
and independent copies are supplied by the product of an arbitrary real
probability law; `max_weight_iid` also transfers the bound to iid random
variables on any probability space by proving their joint product law.
Bounded support records that the support diameter is
finite, since mathlib's real-valued diameter is totalized on unbounded sets.

The completed small-ball bound has the form

```text
P(|sum_{j in S} y_j - center| <= rho)
  <= 4*m/(n-d+1) + exp(-c*d).
```

The positive-degree proof holds for every `d <= n` when `|K| >= n/2`;
the manuscript target retains its `d <= n/2` hypothesis and includes
degree zero by the trivial probability bound of one. Here
`c = 3*log(3/2)/4 - 1/4 > 0`. Exact-slice factorial moments come from a
bijection counting supersets, rather than an independence assumption
about coordinates within a row. The target permits real-valued `m` as
in the manuscript, with downward rounding preserving the coefficient.

The measure bridge proves `rowSliceMatrixLaw_eq_pi`, with no product-law
assumption added. `rowSlice_uniform_tensorization` applies the new source
estimate to that same finite counting law. The covariance calculation
also checks the dependence inside each row: for distinct coordinates,
`Cov(X_i,X_j) = -p*(1-p)/(n-1)`. For complex coefficients with zero sum,
the centered row's second moment is
`bulkScaleSq/(n-1) * sum_j |a_j|^2`.

The conditioning argument proves its model correspondence explicitly.
`sliceOfEmbedding` sends an injection to its support; the fiber has `d!`
elements, by an equivalence with embeddings into the fixed support.
For `K` rows, these fibers have `(d!)^K` elements. On distinct samples,
the with-replacement matrix equals the slice matrix entry by entry.
`condition_matrix_event_to_slice` therefore applies to actual matrix
events without an assumed correspondence. Under `2*d<=n`, its factor
is at most `exp(2*K*d^2/n)`. `DegreeRates.lean` proves that the logarithm
of the exact factor divided by `n` tends to zero in the lower regime.

The profile occupancy rate is `c = (1-log(2))/2 > 0`. The large-part
failure bound uses independent coordinate samples and disjoint parts;
it does not assume that the different multinomial counts are independent.
For sufficiently large `d`, the polynomial prefactor is absorbed with
rate `c/2`. `ProfileEstimator.lean` then proves the actual-to-truncated
comparison and the dyadic geometric-mean argument for the weights defined
in the manuscript. Its sample-index estimator is proved equal to the
minimum over visited parts, so repeated coordinate samples are accounted
for. The first averaged-estimator inequality has constants `epsilon=1/12`,
`C=4`, and rate `min(log(2)/4, (1-log(2))/4)`. The closed target makes the
absolute large-degree threshold explicit:

```lean
example : CircularLaw.AveragedEstimatorLemma := CircularLaw.averaged_estimator_lemma
```

`ProfileRange.lean` proves the weight bounds and the dyadic support-diameter
estimate from positive integer heights bounded by the ambient dimension.
With logarithmic lower constant at least `96`, the averaged-estimator
inequality holds eventually, uniformly over these profiles. This includes
the proof that degrees tend to infinity and that the Chernoff prefactor
can be absorbed. The canonical decomposition and its height bound now
discharge the profile hypotheses in `eventually_canonical_profile_estimator`.
The spread-sum estimates and the averaging of the conditional row bound
are now proved in `SpreadBlock.lean` and `AveragedRow.lean`, completing the
**full averaged-profile proposition**, including its concentration conclusion
and deterministic scalar shifts.

The dyadic random variable is defined on a uniform coordinate as
`floor(logb 2 (truncatedWeight (part coordinate)))`. Parts that have the same
dyadic value contribute their combined masses to that value's probability.
Thus equation `eq:B-distribution` is interpreted as selecting a part with
mass `p_q` and then taking its dyadic weight; its displayed probability
formula requires this mixture interpretation when bins coincide.

The count-conditioned law is now checked by an explicit equivalence between
the profile fiber and the product of a label-assignment space with the block
sample spaces. The row sum is independent of label ordering under this
representation. `conditional_profile_independent_samples` proves both the
independence between parts and the independent uniform samples within each
part; it does not assert independence of the original sample positions
after conditioning on their counts. `withReplacementMatrix_mulVec` proves
that this sum is the actual bilinear matrix row action.

`PlanarPacking.lean` proves the maximum atom bound from the factor-four
level-size balance. Disjoint complex disks give the sharp packing bound.
For `d>=65536`, this verifies the single-summand bound `5/6` for heights at
least two, and the bound `1/2` for heights greater than `32` in the reduced
range `tau^2<=h*sqrt(Q)`, with `Q<=d`. These are hypotheses for the planar
concentration estimates used in [LLTTY19, Propositions 2.2 and 2.3](https://arxiv.org/pdf/1801.05575v4#page=10).
**Propositions 2.2 and 2.3 now have complete Lean proofs.** The discrete
estimate in Proposition 2.5 is proved separately as described above. The conditional
row proof's regular block bound now follows from it in `RegularBlock.lean`.
The general assembly theorems retain block bounds as arguments for reuse.
`ConditionalRow.lean` and `AveragedRow.lean` discharge those arguments for
the actual canonical parts, completing both named manuscript results.

[`paper-coverage.json`](paper-coverage.json) maps all 29 named results to
their source statements, target declarations, proofs, and unresolved work.

## Tensorization statement review

The closed source proposition is checked by

```lean
example : CircularLaw.TensorizationSourceLemma := CircularLaw.tensorization_source_lemma
```

For independent complex random variables and nonnegative `t` and `A`,
the assumption `Q(X_i, sigma*t) <= A*sigma^2` for every `sigma >= 1`
implies, for every `tau >= 1` and deterministic centers `z_i`,

```text
P(sum_i |X_i-z_i|^2 <= tau^2*t^2*K)
  <= (4*exp(1)*A*tau^2)^K.
```

The expectation estimate, measurability, integrability, exchange of a
summable series and an integral, product factorization, and Markov step
are all proved. Radius zero is handled by the product of point events.
The nonnegative-radius convention is explicit in the Lean target.

The original manuscript had `C*tau^2*t^2*K` in the threshold and reuses
the same `C` on the right. Interpreted as one fixed constant, this is false:
take `K=2`, `t=tau=1`, and two independent uniform complex disk samples
of radius `R`, with `R^2 >= 2*C`. Then `A=1/R^2` satisfies the concentration
assumption, but the event probability is `2*C^2/R^4`, exceeding the
claimed `C^2/R^4`. This counterexample explanation is not itself a Lean
formalization of the disk law.

The cited [LLTTY19 Lemma 2.7](https://arxiv.org/pdf/1801.05575v4) uses
threshold `epsilon^2*K` and a separate absolute constant in the bound.
The source form above is proved. The user approved the exact correction
on 2026-10-10, and it is applied. The source mapping and hashes are updated;
`lem:tensorization` is proved and included in the final count of 29/29.
The exact applied patch is retained in
[TENSORIZATION_CORRECTION.patch](TENSORIZATION_CORRECTION.patch).

## Full target and proof status

`CircularLaw.MainTheorem` in `Statement.lean` defines the exact main target.
`CircularLaw.main_circular_law_theorem` in `CircularLawProvedRegimes.lean`
is its unconditional checked proof. It gives one absolute `C > 0` such
that every degree sequence with eventual `C*log(n)<=d(n)` and `d(n)/n->0`
has its variance-normalized ESD converge to the circular law in probability.
Both degree regimes and every input to their assembly are supplied.

The actual uniform law on complete tuples of supports is proved to give
independent uniform rows. Characteristic roots count algebraic
multiplicity, and every positive bounded-Lipschitz deviation probability
tends to zero. The main degree hypotheses eventually ensure nonempty
slices and a strictly positive bulk scale.

The exact target mapping and proof route are documented in
[CIRCULAR_LAW_STATEMENT_REVIEW.md](CIRCULAR_LAW_STATEMENT_REVIEW.md).
Both quantitative joint minimum estimates are independently proved in
`JointSmallestSingularTheorems.lean`; their targets use the actual matrix
laws, non-strict smallest-value events and reviewed source quantifiers.

## Completed proof obligations

All 29 named results are proved. The strict completion gate, full project
build, axiom audit and eight integrity tests pass. The final supporting
addition has 53 checked theorems, nine definitions and one parameter
structure in 14 modules. The source mapping review records the exact
quantifiers, approved corrections and final validation counts.

The rounded auxiliary comparison is replaced by the checked direct
minor-prefix convergence. The approved tensorization and final statement
patches account for all manuscript source changes. Source locators remain
in [sections/appendix_b.tex](../sections/appendix_b.tex), and the historical
proof development is recorded in [DEPENDENCIES.md](DEPENDENCIES.md).
