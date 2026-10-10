# Full-paper proof obligations

The objective is to prove the manuscript's claims with their actual
hypotheses and conclusions, culminating in `CircularLaw.MainTheorem`.
Proving a conditional reduction does not discharge its assumptions.
Every imported mathematical result must ultimately be supplied by a
checked proof, whether from mathlib or new development. No source result
is declared as a project axiom.

Current completion status: **all 29 named manuscript results are proved**,
including the main theorem, both degree regimes and both quantitative
joint minimum estimates. Every required mathematical input is supplied
by a checked proof. The approved source corrections resolve the
statement review issues. The full build, axiom audit, strict completion
gate and eight integrity tests pass. The detailed entries below record
earlier proof milestones and source interfaces; they do not claim full
formalizations of every paper cited by the manuscript. See
[CIRCULAR_LAW_STATEMENT_REVIEW.md](CIRCULAR_LAW_STATEMENT_REVIEW.md).

The following are the source interfaces recorded by the manuscript's
[dependency ledger](../sections/appendix_b.tex). The required interfaces are proved in this
Lean project. Their source locators describe the manuscript's dependencies;
this file does not claim the cited preprints have been fully formalized.
Checked portions of these interfaces are described below.

| Source | Interfaces required by the manuscript | Used for |
| --- | --- | --- |
| Li–Litvak–Yu, arXiv:2604.10446v1 | Theorem 1.3; Theorem 1.7 and Remark 1.9; Theorem 3.1 and Remark 3.2; Theorem 4.1 | Higher-degree circular law; row-slice and Bernoulli smallest singular values; rectangular restricted norm |
| LLTTY19, arXiv:1801.05575v4 | Section 4.1 equation (8), Lemmas 4.5 and 4.11 | Shifted steep classes, steep nets and almost-constant reduction are checked for the manuscript's actual classes |
| LLTTY19 | Lemmas 5.1, 5.4, 5.5, 7.2, 7.7–7.9 and Theorem 5.6, including intermediate conclusions extracted in Appendix A | Canonical approximation, decomposition, factorial and geometric bounds, clustered class sums |
| LLTTY19 | Propositions 2.2 and 2.3; Lemma 6.4 | Planar concentration and conditional row-local small ball |
| LLTTY21, arXiv:1801.05576v2 | Theorem 4.2, Propositions 4.4 and 4.7, Lemmas 4.8–4.10 | Fixed-subspace Gaussian anti-clustering is checked in the standing manuscript band; a coarser upper-coordinate argument replaces the general Proposition 4.7 |
| Rudelson–Tikhomirov | Sparse iid circular law under the minimal divergence condition | Comparator theorem |
| SSS25, arXiv:2310.17600v2 | Facts 10.1 and 10.2, Lemma 8.2, Fact 9.1, Lemma 9.3 | Shifted Gaussian singular-value law and the full Bernoulli logarithmic-potential squeeze |
| Tao, *Topics in Random Matrix Theory* | Theorem 2.1.13 | Convex concentration at a median for bounded independent complex coordinates |
| Tao–Vu | Theorem 2.1 | The probability version used by the manuscript is proved, connecting actual log determinants and Hilbert--Schmidt bounds to full BL-distance convergence |

The source formulas, parameter ranges, and adaptations must be stated
precisely in Lean before their proofs can be connected to the paper.
The manuscript's deterministic consequences of these sources are also
proof obligations; source citations alone do not prove those consequences.

LLTTY19 Lemma 2.7's source tensorization estimate is proved in
`CircularLaw.TensorizationSourceLemma`, with constant `4*exp(1)` in the
probability bound and coefficient one in the squared-radius threshold.
The manuscript's reuse of one identical constant in both places needs
correction or an explicit distinct-constants convention before its named
lemma can be counted as complete. See the statement review in
[DEVELOPMENT_HISTORY.md](DEVELOPMENT_HISTORY.md#tensorization-statement-review).

Both sides of singular-value interlacing under row and column deletion and
the exact principal-minor shift are checked. Extended logarithms preserve
infinite values at singular matrices, the probability-limit deductions are
checked, and the ESD transfer from square-root-degree normalization to
variance normalization is proved below. Identification of the Gaussian limiting logarithmic integral,
remaining minor-prefix and upper estimates and sparse
i.i.d. circular law still require checked proofs. The actual Gaussian
weak law at every shift is constructed below.

The Section 4 equal-block mechanism now has checked proofs for the actual
row-slice exposure and independent uniform singleton positions across both
blocks and rows. `SingletonExposure.lean` represents the exposure by the
active singleton mask and all fixed support positions; the latter also fix
every non-singleton block count. `SingletonExposureConcentration.lean`
transports the one-half and checked Esseen bounds to this exact fiber.
`FiniteProductFibers.lean` proves the joint row exposure's product law and
the exact restriction to selected rows. `IndependentLogTail.lean` proves
the binomial logarithmic exponent, and `WitnessSelection.lean` proves the
incidence count and selected-row lower bound. `EqualBlockWitnessNorm.lean`
consequently proves both Euclidean norm bounds on the corresponding
selected-block witness events, including every constant-vector and
diagonal shift. No conditional independence or concentration conclusion
is an extra hypothesis of these estimates. `OrderedBlockGeometry.lean`
constructs the actual top/tail blocks from the decreasing-norm permutation.
`EqualBlockScale.lean` verifies the literal floor scale and quotient
rounding. The remaining parameter modules give the absolute large-block
threshold, the one-half probability bound and the logarithmic rate.
`EqualBlock.lean` closes the full named lemma: both estimates keep the
uniform witness event inside the probability, use the actual full-matrix
law and retained shifted matrix action, and have common positive norm and
rate constants. The surrounding polylogarithmic upper degree bound gives
the finite scale conditions for every sufficiently large dimension; the
logarithmic lower bound and shift restriction are not needed for this
stronger estimate. The threshold is uniform in the vector, constant shift,
diagonal shift, retained set and degree.

`WitnessSliceCount.lean` and `RowWitnessProbability.lean` count the actual
singleton row events. `SingletonWitnessLower.lean` obtains lower probabilities
from the one- and two-coordinate laws by the deterministic alternative that
another coordinate is selected. `IndependentLowerTail.lean` and
`WitnessCountTail.lean` then apply independence across rows to those probabilities.
`DisjointSetPairs.lean` gives the exact pair count and `BinomialEntropy.lean`
proves the required entropy estimate directly from the weighted binomial theorem.
The uniform witness failure modules keep the actual retained or eligible rows
and give the source equal-block failure form. `WitnessDegreeRates.lean`
absorbs the floor-scale entropy and proves the `exp(-c*n)` bound uniformly
under the surrounding degree assumptions. `OrderedPrefix.lean` constructs
the top coordinate sets from the actual vector; `UniqueWitnessAction.lean`
and `SteepWitnessExclusion.lean` give the shifted `T0` witness mechanism
and simultaneous ordered-jump kernel exclusion. `FirstScaleWitnessFailure.lean`
closes the actual ceiling-scale witness failure at rate `exp(-c*n/sqrt(d))`.
The steep scale modules implement the literal floor stride, least starting
exponent and final exponent, geometric pairs and terminal ceiling. They verify
both codimensions, row counts, size and density bounds, entropy absorption and
the scale-count prefactor throughout the source degree band.
`SourceSteepClasses.lean` gives the actual recursive first-jump classes, and
`SourceSteepExclusion.lean` proves the full shifted `T0` exclusion and its
`exp(-c*n/d^3)` bound simultaneously for all allowed spectral shifts.
`OrderedNormStability.lean` proves the coordinate perturbation and constant-shift
bounds for the actual sorted moduli. `SourceVerySteepInclusion.lean` proves
the permitted shifted `T3` inclusion, with source constant `0.9` and the actual
floor normal rank. `SourceNoSteep.lean` checks the recursive alternatives,
including nonzero vectors with zero first-scale modulus. The almost-constant
modules prove the count-based center and translated-tail bounds, the source
rank ordering with every floor retained, and the full named deterministic
reduction in both tail cases. `LowerBandEventually.lean` and
`UniformSourceKernel.lean` make the thresholds uniform over every degree in
the literal lower band, both codimensions and the whole spectral window.
These inputs are assembled with the checked `T1`/`T2` nets, row-load
exclusion and gradual normalization into full rectangular kernel compatibility,
as described below.

The Section 3 Chernoff input is now derived from the finite independent
sample law in `Binomial.lean`, including the multinomial large-part union
bound and prefactor absorption. `Conditioning.lean` proves the exact
distinct-sampling pushforward to uniform supports and the matrix-event
transfer factor; `DegreeRates.lean` proves the claimed subexponential
conditioning cost in the lower regime. `ProfileEstimator.lean` proves the
actual-to-truncated estimator comparison, the dyadic geometric mean, and
the first averaged-estimator conclusion, including its absolute degree
threshold. `ProfileRange.lean` verifies the truncated-weight bounds and
support diameter from the profile definitions and proves the eventual
estimator bound under logarithmic degree. The canonical vector decomposition
is now constructed and verified as described below. Both spread-sum branches,
the full conditional row lemma, and both averaged-profile conclusions are
now proved in `SpreadBlock.lean`, `ConditionalRow.lean`, and `AveragedRow.lean`.

`FiniteConditioning.lean` proves finite disintegration and the convolution
concentration bound. `ProfileConditioning.lean` proves the actual count-fiber
representation, including the independent uniform law on all block samples,
and the conditional/averaged row assembly with the geometric block bounds
as explicit arguments. `PlanarPacking.lean` proves the balanced-level atom
bound and the disk-packing estimate, and checks the single-summand hypotheses
for the low- and high-height spread branches at an absolute degree threshold.
The full sum-concentration conclusions of LLTTY19 Propositions 2.2 and 2.3
are now proved for arbitrary independent planar laws. Esseen uses Gaussian
Fourier integration, symmetrized deficits, periodic cosine integration, and
weighted Jensen under the actual moment-tilted law. Miroshnikov uses actual
translated squares, the first integer half-mass scale, localized convolution,
the checked Esseen estimate, and strong induction on the number of summands.
The square/disk comparison preserves exactly `sqrt(2)*r` in the maximum
single-summand concentration. Both targets also include independent random
variables on arbitrary probability spaces; neither concentration conclusion
remains a proof assumption. Their exact statements are on printed page 10 of the cited
[v4 source](https://arxiv.org/pdf/1801.05575v4#page=10).

The Fourier-power argument supporting Proposition 2.4 is now proved with
absolute constant `200` in place of the source's numerical `47`:
`bounded_density_fourier_power_lemma` applies to arbitrary planar probability
densities bounded by one almost everywhere. `CharacteristicDefect.lean`
proves the integer dilation estimate by symmetrization, and
`FourierLevels.lean` proves the superlevel-area estimate and power decay.
`FourierPlancherel.lean` identifies mathlib's L2 Fourier transform with the
classical Fourier integral for all L1/L2 inputs by equality against test
functions. `BoundedDensity.lean` consequently derives the energy bound
from the density hypotheses. `FourierProduct.lean` proves integrability
and the `200/m` integral bound for products of `m>=2` such Fourier moduli.
No Plancherel identity or energy bound is added as an assumption to the
closed bounded-density lemma. `FourierInversion.lean` proves almost-everywhere
classical inversion. `DensityMeasure.lean` constructs and reconstructs the
Radon--Nikodym density of the sum, and `SumLaw.lean` proves its characteristic
function is the product of the summand characteristic functions.
`independent_planar_density_lemma` in `PlanarSumDensity.lean` consequently
proves Proposition 2.4's actual density conclusion in the complex plane,
with constant `200/m` for all `m>=1` and independent summands on any
probability space. Its small-ball corollary uses the area of a closed disk.
This closes Proposition 2.4. Propositions 2.2 and 2.3 are also closed by
the Esseen and Miroshnikov developments described above.
The Fourier argument is on printed pages 11--12 of the
[v4 source](https://arxiv.org/pdf/1801.05575v4#page=11).

`independent_planar_discrete_lemma` in `DiscreteConcentration.lean` proves
Proposition 2.5 with absolute constant `10000`. Its conclusion is
`Q(sum,t) <= 10000*max(u*t^2/(m*delta^2),u)`, for `m>=1`, positive separation
and atom bounds, and nonnegative radius. It applies to independent
summands on any probability space whose actual marginal laws are
concentrated on separated points; identical distribution is not needed.
`PlanarDensityScale.lean` checks the arbitrary-density scaling.
`PlanarDisk.lean` constructs the noise and proves its mean and moment bound;
`IndependentSecondMoment.lean` proves the additive moment identity and
the noise probability lower bound `3/4`. `DiskSmoothing.lean` proves the
smoothed density bound by translation and Tonelli. The convolution law
and probability comparison in `ConvolutionConcentration.lean`, followed
by the atom bound in `SeparatedLaw.lean`, complete the argument without
assuming a noise tail estimate. The iid case is exactly the interface
needed in the manuscript's regular-part branch. `RegularBlock.lean`
proves the bound for actual uniform block samples from balanced levels
with `1/k` separation: radius `tau*sqrt(d)/k` yields the upper bound
`40000*tau^2/(h*m/d)` for `1<=m<=d` and `tau>=1`. Its independent law
and the geometric scale are both checked. `SpreadBlock.lean` completes both
spread-sum branches with the exact weight `h*sqrt(m)`, including the source's
large-`tau` reduction to the trivial probability bound.
The source's statement and smoothing proof are on printed pages 10--11
of the [v4 source](https://arxiv.org/pdf/1801.05575v4#page=10).

The canonical construction from LLTTY19 Section 5.2 is now checked.
`Discretization.lean` proves the literal floor formula, its equivalence
with the scaled integer-lattice definition, its error bound, and the
`1/k` separation of distinct lattice values. `LevelSlices.lean` and
`LevelPartition.lean` implement the leftmost-level procedure, prove its
size bounds, disjointness, exhaustion, and factor-four balance.
`CanonicalRemainder.lean` proves that this per-level recursion is exactly
the global remaining-coordinate procedure and that its represented values
are the image of that remainder.

`GreedySpread.lean` uses the lexicographically greatest value with a
separated partner as its seed, followed by a decreasing admissible scan.
Separation, covering, the two-value minimum, and the no-separated-pair
case are proved. `CanonicalParts.lean` constructs both kinds of parts,
checks their size-height bounds and regular-value geometry, and gives an
explicit fiber equivalence proving their level balance.
`LevelInvariants.lean` proves nested represented values and the source
height and size invariants under coordinate permutation.
`CanonicalPartition.lean` constructs the actual disjoint-cover profile.
`CanonicalProfile.lean` enumerates spread parts first in increasing order,
then regular parts in increasing order, and proves the eventual `3*log(n)`
part-count bound and the dimension bound on heights.

`CanonicalRow.lean` applies the regular bound to the actual profile fibers
and hence to the exact count-conditioned row sum. It also applies the
averaged estimator to the ordered canonical profile, with its height
hypothesis discharged. `CanonicalSpread.lean` derives the two spread
single-summand hypotheses from the constructed parts. `CanonicalSpreadSum.lean`
applies the now-proved sum estimates to these parts and the exact profile
fibers. `ConditionalRow.lean` closes the conditional row lemma with no block
estimate as an argument. `AveragedRow.lean` proves both averaged conclusions
and deterministic scalar shifts; `ProfileTensorization.lean` proves the
actual matrix Euclidean norm estimate, deterministic vector shifts, and
conditioning to uniform row slices. Canonical factorial compression is
now proved as described below, together with the actual class-size formula.
The actual class-count bound in the standing lower band is also proved
as described below. The clustered-Pv separation and full deterministic
package are checked below; the gradual net probability sums remain open.
The source construction and invariants are on printed pages 35--37 of the
[v4 source](https://arxiv.org/pdf/1801.05575v4#page=35).

The source weight-entropy lemma is now proved in `WeightEntropy.lean` for
every integer probability law, with constant `2+log(4)`. Countable entropy,
the infinite-dispersion case, and the independent-copy expected-distance
identity are checked. `FiniteWeightEntropy.lean` and `DyadicWeightEntropy.lean`
identify the actual uniform-coordinate dyadic law and its pair dispersion.
`EntropyCancellation.lean` proves the uniform analytic penalty and
exponential cancellation for `K>=n/2`. `MultinomialEntropy.lean` proves
the exact factorial entropy inequality from the weighted multinomial
theorem, including zero bins and zero total count. `IntegerHistogram.lean`
and `DyadicHistogramEntropy.lean` supply the actual counts, their exact
entropy exponent, the source dyadic intervals, and bin-factorial cancellation.
`ProfileFactorialEntropy.lean` gives the part-size sums, factorial product
regrouping, and global comparison/entropy/cancellation from local bin
compression. `ProfileLogGeometry.lean` proves the exact log formulas for
the four truncated-weight families and exponential size decay within a
fixed bin. `FourFamilyEntropy.lean` converts these tails into a uniform
entropy bound; `ProfileBinCompression.lean` proves local compression with
constant `4096`. `ProfileSmallBinMass.lean` proves total size at most `512*T`
for any subset of one bin with individual sizes below `T`.
`CanonicalBinCompression.lean` supplies the geometry from the actual
canonical and ordered canonical partitions, identifies the literal
coordinate union, and closes both estimates in part (iii) of the LLTTY
package. It also closes canonical factorial entropy and dispersion
cancellation without an additional compression hypothesis. The
class-size formula from Lemma 5.5 is now proved in
`CanonicalClassCardinality.lean`: equality of coordinate multisets gives a
coordinate permutation, part data are invariant, and an injective encoding
by fixed-size assignments and permitted coordinate values gives the exact
factorial/height bound. This holds for every restricted canonical
approximation family. Subfamily class counts cannot increase when the
larger class family is finite. `CanonicalClassEntropy.lean` combines the
actual class-size bound with entropy cancellation and the actual inverse
truncated weights, leaving the source height/weight product. The
`exp(n)` class-count conclusion needed from Lemma 5.1 is now proved
directly in `UniformGradualClassCount.lean` in the manuscript's standing
lower degree band. The actual gradual approximation families and their
multiset-class families are finite. One dimension threshold covers both
admissible codimensions, every source discretization scale and every
restricted subfamily, with `0<a3<=1/65536`. The proof counts multisets
in four literal rank blocks by stars and bars, counts the actual rounded
grid alphabets, and absorbs all four entropy costs. The logarithmic lower
bound is used for the initial block; this proof does not claim the broader
degree scope of the external lemma. The full five-part LLTTY package is
now proved, including the K1/K2 and clustered-Pv estimates below.

The deterministic refinement input is now proved for the actual canonical
approximations. `ApproximationRefinement.lean` proves exact floor composition
and finer-level inclusion. `LevelSliceCounts.lean` proves survival thresholds
and prefix counts; `LevelRefinement.lean` proves uniqueness of majority
levels and factor-eight prefix-mass transfer. The nine-cell coarse-grid bound
in `FloorGridCover.lean` yields the actual greedy spread-height estimate.
`RefinementSpread.lean` transfers heights to coordinate masses, and
`RefinementMassDichotomy.lean` proves the unconditional coarse high-height
mass bound by 288 times finer spread mass plus 41 times shrinking count.
`SeparatedOrderDichotomy.lean` proves the high-height/spread alternative from
separated cohorts and the resulting actual-scale spread/shrinking dichotomy.
The gradual-class cohorts are now constructed by actual real and imaginary
quantiles in `PlanarQuantileCohorts.lean`, with the source `k>=5/theta0`
scale. `GradualRefinementDichotomy.lean` removes the cohort premise.
`SourceRefinementFamilies.lean` retains the literal `Ku` spread-mass and
`Pv` exponential height definitions. `AccumulatedShrinkage.lean` and
`GradualLevelAccumulation.lean` prove the many-coordinate contraction;
`LowHeightCoordinates.lean` transfers small final levels to actual
high-height mass. `GradualDecomposition.lean` proves the exact union
through every `v>=5`, with `cK=1/4608` and `cP=1/65536`, closing part (i)
in the manuscript's standing setting. One large-dimension threshold is
uniform in `v`, the codimension parameter, and every degree above the
logarithmic lower bound. The one-step threshold `n3/656` suffices for these
positive constants; the external Lemma 5.9 numerical threshold `n3/192`
is not claimed. The K1/K2 branches are now proved for the actual families
and truncated weights. `ProfileCutoffProduct.lean` proves the exact
three-family product calculation. `SourceK1Product.lean` supplies the
actual spread mass and keeps the floor correction in `n3`, yielding
`d^(-(cK*a3/32)*n)` once `a3*n>=4`, together with the class entropy
consequence. `IntegerOrderQuantiles.lean` and `ProfileK2Separation.lean`
combine the actual `512*d^(-kappa)*n` per-bin bound with rounded
coordinate quantiles. `SourceK2Separation.lean` gives both probability
tails at least `cK*a3/32` and a gap at least
`(cK*a3/16384)*d^kappa`, uniformly in all scales and codimensions for
every degree above `C*log(n)` once `n` is large. The common positive
constant `cK*a3/16384` supplies both product decay and gap in the combined
part (iv) statement, and the product prefactor can be `C=1`.
`SourceClusterLowTail.lean` proves the clustered low-tail mass `delta/36`
from the actual closed cluster, a repeated rounded value and the last
nonempty level chunk. The actual high-height family has mass at least
`cP*a3*n/2` for large dimension. `ProfileHighHeightBins.lean` and
`SqrtHeightCutoff.lean` bound the portion below `H/(d*sqrt(cP*a3))` by
`512*(2-log_2(cP*a3)/2)*d^(-1/3)*n`, using actual small-part bins.
This leaves upper-tail mass at least `cP*a3/4` at large degree.
`SourcePvSeparation.lean` combines it with exact integer floors to give
the manuscript gap under its original separation hypothesis. Its
threshold is uniform in every scale and codimension.
`SourceLLTTYPackage.lean` assembles all five parts into the full named
target, with `c0=cP*a3/4`, `c1=cK*a3/16384` and common `C=4096`, for
`0<a3<=1/65536`. The construction keeps the literal families, actual
canonical approximations and classes, both admissible codimensions,
class-count scale conditions and original clustered-Pv hypotheses.
The gradual-net probability exclusions and structural theorem are now
checked by the later modules described below.

The fixed-vector Section 5 estimate now follows from the checked profile
tensorization with its actual canonical weight range. `FixedNetSlice.lean`
proves the literal `R*log(d)*sqrt(d*n)/k` radius and a uniform dimension
threshold. `FullMatrixFixedNet.lean` uses the exact restriction of the full
independent row law and Euclidean reindexing, so the bound applies to every
deterministic retained set and vector shift.
`ProfileMeanPowers.lean` proves the exact geometric-mean power identity
and the missing-row cost `(n*sqrt(d))^L`. The two separated source tails
give checked K2 and clustered-Pv dispersion lower bounds in
`SourceProfileDispersion.lean`. `ClassRowEnergy.lean` and
`SourceClassRowEnergy.lean` combine the actual class size and entropy
cancellation with these bounds and the K1 product estimate, at the literal
row count `K=n-L`. The finite row-count conditions are derived for both
source codimensions.

`CanonicalClassStatistics.lean` proves invariance of the actual profile
statistics by equal part sizes, masses, heights and spread/regular kinds.
This accommodates the leftmost-occurrence selection at repeated values.
`CanonicalClassProbability.lean` gives the actual class probability sum
and event union. `FixedNetSplit.lean` separates the dispersion and
profile-exception terms, and `CanonicalClassSplit.lean` supplies the three
branch bounds at the actual row count.
`CoordinateClassSummation.lean` proves exact regrouping of the original
finite family by its represented classes. In `CanonicalFamilyProbability.lean`,
the dispersion term uses the checked `exp(n)` class count and the exception
term uses exactly the family cardinality. `SourceFamilyProbability.lean`
discharges every class-energy input for actual K1, K2 and clustered-Pv
restricted approximation families. Its uniform statements retain the
displayed class-count scale range, original cluster separation hypotheses,
and all conditioning and missing-row costs.

`TwoAlphabetCounting.lean` and `GradualNetCounting.lean` prove the actual
crude approximation count by top-coordinate positions and two finite
alphabets. `GradualNetEntropy.lean` gives its uniform
`exp(128*n*d^(1/3))` bound. `StructuralParameters.lean` retains the literal
growth, radius, cluster fraction and terminal floor, supplies the
discretization logarithm budget and proves the terminal-radius comparison.
`StructuralDiscretization.lean` checks every scale through the actual `vL`
against the required `sqrt(n)/d^(3/2)` range in the manuscript's degree band.
`StructuralNetUnion.lean` proves the actual all-scale cardinality bound
`vL*exp(128*n*d^(1/3))`.
`ProfileExceptionCost.lean` bounds the actual conditioning and row factors
and absorbs the crude approximation entropy.
`ProfileExceptionUnion.lean` sums the exception contribution over all
terminal scales, including the displayed `2*d^2` prefactor, with bound
`exp(-(averagedProfileRate/8)*n*d^(2/3))`. Its threshold is uniform for a
fixed radius constant. `SourceTerminalProbability.lean` applies the scale
fit and exception absorption to the actual K1 and K2 family probability
sums.
`MissingRowCost.lean` derives the actual missing-row factor bound
`(n*sqrt(d))^L<=exp(n)`, and `LogarithmicNetCost.lean` retains the row cost's
`log(log(d))` exponent. `StructuralBranchEnergy.lean` absorbs the class
count, conditioning and missing-row costs into the actual K1 and K2
decay rates. `FiniteProbabilitySupremum.lean` proves attainment of every
shift supremum and a simultaneous maximizing shift assignment for a finite
family. `SourceSpreadProbability.lean` therefore bounds the manuscript's
actual sum of suprema and combines the two mass cases covering the full
spread family. `SourceSpreadScaleSum.lean` closes the full terminal-scale
sum, including the displayed `2*d^2` prefactor, with rate
`exp(-(sourceK1DecayExponent(a3)/4)*n*log(d))` uniformly in the standing
degree band and both codimensions.
The terminal clustered parameter budgets are also checked:
`TerminalClusterParameters.lean` retains the actual floor and proves the
cluster-margin lower bound, and `TerminalClusterBudgets.lean` absorbs
every fixed logarithmic cost. `TerminalPvHypotheses.lean` verifies the
literal source separation hypotheses uniformly.
`TerminalPvEnergy.lean` absorbs the actual class, conditioning and
missing-row costs. `TerminalPvProbability.lean` uses the strict source
cluster inequality and the actual canonical approximation family to
bound the full sum of fixed-vector shift suprema.
`TerminalPvPrefactor.lean` includes the displayed `2*d^2` prefactor with
bound `exp(-(sourcePvDecayRate(a3)/4)*n*deltaL*vL)` plus
`exp(-(averagedProfileRate/8)*n*d^(2/3))`.
`CenteredCanonicalApproximation.lean` and `ScalarMeanGrid.lean` now prove
the actual centered rounding error and finer scalar cover, with at most
`d^2` scalar values. `CenteredSliceAction.lean` proves the exact shifted
kernel identity and action bound on the actual retained centered-norm
event. `CanonicalNetKernelCover.lean` and
`CanonicalKernelProbabilityReduction.lean` give the continuous-vector
cover and the source probability inequality with the full sum of shift
suprema. The actual norm failure probability is retained explicitly.
`TerminalKernelProbability.lean` combines the continuous spread and
clustered terminal kernel probabilities with their source decay terms;
the shared norm failure is counted once over the spread-scale union.
`SourceNormalCoordinates.lean` bounds the literal starting-rank modulus
by `d^16` and passes this to every later valid rank, including the floor
normal rank. `StructuralNormalRadius.lean` proves the uniform structural
radius comparison and cluster-centre rescaling. Its direct polynomial
envelope avoids asserting the manuscript's intermediate
`d^3*(n/qL)^6` inequality.
`StructuralKernelAlternatives.lean` checks the exact two structural
alternatives and assembles their failure probability from actual kernel
compatibility and terminal-family events. The remaining bound contains
`4/n`, three exponential terms, and twice the actual restricted-norm
failure probability. `StructuralFailureBudgets.lean` absorbs every
terminal exponential term into `n^-2`. The source structural alternatives
therefore have probability at least `1-5/n` conditional on the actual
norm failure being at most `n^-100`. `RestrictedNormRetained.lean` now
proves that actual estimate under `103*log(n)<=9*d`.
`RestrictedNormUniform.lean` supplies it uniformly throughout the source
degree band. `NetReductionTheorem.lean` completes the full named
net-reduction target for every gradual subfamily. The actual conjugated
retained-row span has orthogonal complement equal to the shifted matrix
kernel by `RetainedRowOrthogonality.lean`. `StructuralKernelTheorem.lean`
chooses fixed admissible constants and proves the exact source structural
theorem, uniformly in both codimensions, every deterministic retained set,
and each fixed spectral window, with probability at least `1-5/n`.

The weighted concentration input to the restricted-norm proof is checked
in `WeightedSliceLaplace.lean`, `WeightedMatrixLaplace.lean`,
`WeightedMatrixConcentration.lean` and `SignedMatrixConcentration.lean`.
Containment probabilities bound the exact weighted generating function
by the Bernoulli product for nonnegative weights. Complementing the exact
slice treats negative tilts. The independent row product gives the
centered exponential moment with squared-weight variance proxy.
Finite Markov and bounded-tilt optimization give two-sided concentration.
Splitting signed coefficients into positive and negative parts gives
`4*exp(-t^2/(16*v+8*K*t))`, where `v` bounds the actual squared-weight
proxy and `K` bounds every absolute coefficient. This supplies a
concentration ingredient for the light part of the Kahn--Szemeredi
argument in [LLY26a, Section 4](https://arxiv.org/html/2604.10446v1#S4),
with its own checked constants. `LightCoupleBounds.lean` and
`LightCoupleConcentration.lean` specialize it to the actual rank-one light
coefficients: at cap `sqrt(N)/n`, their raw sum has tail
`4*exp(-B*n/32)` above `d/sqrt(N)+B*sqrt(N)` for `N>=d`, `N>0` and
`B>=1`, with unit vectors and zero sum on the column side.
`RowSliceEdgeCounts.lean` and `RowSliceEdgeTails.lean` supply exact
rectangular support-intersection counts, their actual mean, Poisson
exponential moments and the upper tail. The fixed-set event
`exp(2)*mu<E` and `c<E*log(E/mu)` has probability at most `exp(-c/2)`.
A minimum over the finite bad sample set supplies the threshold.
The simultaneous discrepancy estimate is now checked in
`EdgeDiscrepancyEntropy.lean`, `RowSliceDiscrepancy.lean` and
`RowSliceDiscrepancyUnion.lean`. The actual binomial counts and the full
size union yield probability at least `1-n^-beta` for the source
parameters `exp(2)` and `2*(beta+4)`, covering the conclusion of
[LLY26a Lemma 4.7](https://arxiv.org/html/2604.10446v1#S4).
`RowSliceColumnBounds.lean` puts every column load below `9*d` with
failure at most `n*exp(-9*d)`. `MatrixDiscrepancy.lean` and
`RowSliceMatrixDiscrepancy.lean` identify the support events with the
literal matrix conditions; they also prove the actual row sums and
edge bounds from row and column degree caps.
`RowSliceNormEvents.lean` charges both failures: for `0<m<=n`, `n>=2`,
positive degree `d<=n`, `A>=0` and `(A+2)*log(n)<=9*d`, discrepancy
with parameter `2*(A+5)` and the row/column cap `9*d` fail with
probability at most `n^-A` under the actual rectangular row law.
Rectangular transfer and finite-net norm assembly are checked below.
The heavy proof in
[Cook--Goldstein--Johnson, Lemma 6.6](https://arxiv.org/pdf/1510.06013)
has been inspected as the source of LLY26a Lemma 4.8. Its level
decomposition now has a checked complete cover in
`NormDyadicLevels.lean`, `NormDyadicMass.lean` and
`NormHeavyDyadicCover.lean`: the actual finite coordinate fibers include
the base level, have total mass at most five for unit vectors, and bound
the actual heavy bilinear sum by their scaled edge counts.
`NormDyadicSums.lean` proves the required finite geometric budgets.
`NormHeavyLevelRatios.lean` checks the exact normalization and column
degree bound. `NormHeavyDegreeSums.lean`, `NormHeavyEntropy.lean`,
`NormHeavyLargeRatio.lean`, `NormHeavyModerateMass.lean` and
`NormHeavySmallMass.lean` now check all five branch bounds.
`NormHeavyCaseAssembly.lean` proves their exhaustive oriented cover
and actual sum budget. `NormHeavySquare.lean` uses the literal
transpose to cover both fiber-size orderings and proves the full square
heavy bilinear bound. Its dimension-independent constant is
`2*C*(25*cap+10/C+40*kappa2/C+80*kappa2/(C*cap*log(cap))+10)`
at threshold `sqrt(N)/n`, with nonnegative matrix entries, row and
column sums at most `N`, discrepancy density `C*N/n`, `C>0`, `N>0`,
`cap>1`, `kappa2>=0`, and vectors of squared mass at most one.
This is our own checked constant for the complete base-zero partition;
the original numerical constant of LLY26a Lemma 4.8 is not claimed.
The original numerical constants of Theorem 4.1 are not claimed.
`NormRectangularPadding.lean`, `NormPaddingDiscrepancy.lean` and
`NormHeavyRectangular.lean` prove literal zero-row transfer of the heavy
bound. `RowSliceHeavyBound.lean` gives its simultaneous actual matrix event
with the checked polynomial failure.

`NormLatticeCardinality.lean`, `NormLatticeRounding.lean` and
`NormLatticeNet.lean` construct a quarter-net inside the real unit ball,
of cardinality at most `128^n`. `NormMeanProjection.lean` proves norm
contraction and constructs the zero-sum right net. `RowSliceLightNet.lean`
charges the literal net-pair cardinality to the light tail.
`NormFiniteNetReduction.lean` and `RowSliceRealNorm.lean` assemble the
real centered operator bound and polynomial failure. The checked
real/imaginary decomposition in `NormRealComplexTransfer.lean` transfers
it to complex vectors. `RestrictedNormTheorem.lean` proves the full named
manuscript norm proposition, with one positive finite constant controlling
both degree threshold and operator norm, and probability at least
`1-n^-A`. `RestrictedNormRetained.lean` proves the precise retained
centered norm input, including its actual `n^-100` tail. No external norm,
net cardinality or concentration result remains assumed by this target.

The fixed-subspace Gaussian dependency now uses an actual normalized law.
`StandardComplexGaussian.lean` and `ComplexGaussianLinearForm.lean` check
the independent variance-one-half real parts, real linear forms,
characteristic function, and unit complex second moment.
`ProjectedComplexGaussian.lean` checks the coordinate product and continuous
projection onto the deterministic orthogonal complement, including its
Gaussian law and actual retained kernel. `GaussianInnerLaw.lean` proves
the exact Hermitian-form law and the projected coordinate-difference law
at scale `norm(P_Eperp(e_i-e_j))`, without excluding zero scales.
`ComplexGaussianDensity.lean` derives `exp(-norm(z)^2)/pi` from the two
real densities. `ProjectedGaussianSmallBall.lean` proves the disk bound
`(r/scale)^2` at arbitrary centres for positive projected difference scales.
`ComplexGaussianRadialTail.lean` now proves the exact radial tail by polar
integration, with the explicit antiderivative and limit at infinity checked.
`GaussianCorrelationSmallBall.lean` closes the fixed-pair input of LLTTY21
Lemma 4.8 for the actual projected vector. `ClusterPairCounting.lean` and
`GaussianClusterAveraging.lean` prove the averaging bound in Lemma 4.9.
`GreedyCorrelationClusters.lean` constructs the source maximal star clusters
with cardinality-first lexicographic indicator-vector order, their
representatives and the first-small-cluster exceptional set. It checks the
disjoint partition, decreasing sizes, cluster-count bound and bounded
correlated-neighbour count outside that set. `GaussianGreedyClusters.lean`
applies the actual Gaussian averaging estimate with this premise discharged;
it also checks the within-star `(2*alpha,2*beta)` correlation consequence.
`CoordinateDiskEvents.lean` proves closedness and measurability of the disk
events by compact centre projection, so the success probability and the
cardinality conclusion at smaller radii are checked. The source radius and
failure constant are retained; no projected-coordinate independence is
assumed. `GaussianSourceParameters.lean` checks the literal probability and
floor parameters, failure at most `9L/(8n)`, and radius absorption with an
explicit exponent loss of 1024. `GaussianSourceAntiClustering.lean` proves
the full measurable source probability conclusion conditional only on the
required size bound for the actual constructed exceptional set, with one
constant for the final radius and failure rate.
`GaussianRepresentativeCombination.lean` closes the deterministic
equal-representative combination step in Lemma 4.10: the coordinate
difference map has nonzero kernel, normalization gives unit Euclidean
coefficients, and combinations of projected copies stay orthogonal to E.
`GreedyCorrelationOwners.lean` checks the unique star owner and the actual
correlated representative lookup for each exceptional coordinate.
`ProjectedGaussianCopies.lean` supplies the literal product sample law,
independent projected copies, exact marginal and pair-tail laws, and joint
Gaussian law. `CopyClusterCounting.lean` proves the measurable union-count
and Markov estimate with failure at most `2*p*beta` for half the coordinates
to be far from their representative in any copy. No coordinate independence
within a copy is used. `GaussianCombinationClusters.lean` proves the transfer
to all coefficients of Euclidean norm at most one, so sample-dependent
coefficient measurability is unnecessary. `GaussianGreedyCopyClusters.lean`
applies this to the actual greedy exceptional set: a measurable event of
probability at least `63/64` at the source parameters yields a unit orthogonal
combination with a disk of radius `p*alpha` containing more than half the
exceptional set. The count bound `p<=2*n/L` gives failure at most `1/64`.
`GaussianCopiesCombinationLaw.lean` now checks the exact fixed-coefficient
law by nested characteristic functions: the raw vector scale is the
Euclidean coefficient norm, projection commutes, and a fixed unit
combination has exactly the original projected law and all its measurable
event probabilities. `GaussianCoordinateTails.lean` checks the actual
coordinate law, projection-scale contraction and tail `exp(-r^2)`, including
zero scales. Finite coefficient sets satisfy the coordinate union bound.
The actual p-copy law has a measurable event of probability at least
`1-epsilon` on which every coefficient vector of norm at most one has
coordinates bounded by `sqrt(p)*sqrt(log(p*n/epsilon))`, for
`0<epsilon<p*n`. Cauchy--Schwarz supplies the uniform transfer. This is a
largest-coordinate estimate; the sharper ordered-coordinate estimates in
Proposition 4.7 remain open. The lower bound of Proposition 4.4 is checked below.
`GaussianIsometryLaw.lean` checks the exact smaller standard law under a
complex isometric embedding adjoint, then identifies the literal subspace
orthonormal-coordinate map and its projection norm. The actual subspace
squared-norm law is standard in `finrank(F)` dimensions.
`ComplexGaussianNormLaplace.lean` checks integrability and the exact moment
`E exp(t*norm(G)^2)=(1-t)^(-r)` for every `t<1`. Exponential Markov gives
the lower small-ball bound `(exp(1)*u/r)^r` for positive dimension and squared
radius, and upper squared-norm tail `2^r*exp(-u/2)`.
`GaussianProjectionNorm.lean` transfers both bounds and the exact law to
every actual deterministic subspace projection, including the normal.
`GaussianCoordinateDeletion.lean` now checks the actual subspace of normal
vectors vanishing on K. Rank-nullity bounds the dimension loss by `card(K)`;
projection onto that subspace is controlled by the remaining coordinates.
The event that every remaining coordinate has norm at most tau has
probability at most `(exp(1)*n*tau^2/r)^r` in its actual positive dimension r.
`GaussianOrderSmallBall.lean` checks the actual coordinate-subset union and
binomial entropy. For `m>=512`, rank `floor(m/512)` at threshold
`m/(512*n)` has small-ball probability at most `exp(-m/512)`, supplying
the one-vector non-flatness content of Lemma 4.3. Ordered norms are
Lipschitz with constant one by `OrderedNormContinuity.lean`, so their
sublevel events are closed and measurable. `GaussianOrderCombinations.lean`
transfers the fixed-unit law and sums over finite unit coefficient sets.
`ComplexSphereGrid.lean` constructs the actual finite unit sphere cover by
canonical rounding and normalization, with cardinality at most
`(2*k+3)^(2*p)` and radius `4*p/k` for `k>=8*p`.
`GaussianNonflatNet.lean` proves that the bad event for some unit coefficient
is closed by compact projection. The actual net at resolution
`4096*p^2*n^2` passes the finite bound to all unit coefficients.
`GaussianNonflatUniform.lean` absorbs the grid entropy and coordinate-tail
error under the literal source ranges `m>=sqrt(n)` and `p<=n^(1/4)`.
For sufficiently large n, failure is at most `exp(-m/2048)` for some
unit combination to have ordered norm at rank `floor(m/2048)` at most
`m/(2048*n)`. The complementary measurable event gives this positive
lower bound and nonzero output for every unit coefficient vector.
This checks the non-flatness content of Proposition 4.4 with explicit
absolute constant `1/2048`; no Gaussian norm, finite-net or non-flatness
dependency remains assumed in that estimate.
`GaussianSourceRange.lean` now derives the dimension, copy-count, floor-rank
and inverse-codimension bounds uniformly over the manuscript's full standing
degree band and literal interval for L. In particular `log(n)<=n/L` and
`n/L` is arbitrarily large. `GaussianForbiddenComparisons.lean` therefore
bounds every unit combination's largest coordinate by `(n/L)^2/4096` on
the actual coordinate success event at `epsilon=1/64`. With the checked
non-flatness bound, this implies all the required reverse-steepness
inequalities. At correlation exponent 8192 the combination disk radius
fits the structural disk radius. `GaussianExceptionalContradiction.lean`
uses these comparisons to rule out an oversized actual exceptional set
on a common sample of the three success events.
`GaussianAntiClusteringTheorem.lean` proves that such a common sample exists,
discharges the deterministic exceptional-size premise and gives the full
named Gaussian conclusion with absolute constants `a0=1/2048` and 9216.
The latter is used in both radius and failure bound. Every Gaussian law,
non-flatness estimate, finite-net construction, cluster bound and probability
comparison used in this proof is checked. The target explicitly retains the
standing lower-band and constant conventions from Section 2, which apply
throughout Section 6, and has one threshold uniform in d, L and E.
The sharper general upper order-statistic estimates of LLTTY21 Lemma 4.5
and Proposition 4.7 remain unproved; this alternate proof does not need them.

`GaussianRowSpanExtension.lean` checks the literal least-coordinate
projection/normalization enlargement, rank increase, containment and exact
target rank. It applies to every retained conjugated-row span, including
rank deficiency. The enlarged span depends only on the retained rows;
measurability on the finite matrix sample space and joint measurability of
the Gaussian normal are proved. Structural alternatives pass to it, its
normal lies in the retained shifted kernel, and projection norms decrease
under enlargement. The structural probability theorem now has a checked
interface for every fixed `0<a<=1`, with one absolute degree constant
independent of a. The Gaussian admissible normal parameter can therefore
be used in both stages.

`FiniteDiskConcentration.lean` proves that the actual closed-disk
concentration supremum is attained, bounded and measurable.
`GaussianFreshRowParameters.lean` checks both codimensions against the
full Gaussian range, the exceptional fraction, occupancy tail and radius
comparisons uniformly in the source band. `GaussianFreshRowSmallBall.lean`
proves the full averaged normal small-ball estimate with that supremum
inside the expectation and with all probability inputs supplied by checked
theorems. `FreshRowGaussianProbability.lean` uses exact finite coordinate
resampling and Fubini to obtain the actual omitted-row small-ball bound
on the matrix–Gaussian product law, including the diagonal shift.
`GaussianRowDistance.lean` identifies projection norm with metric distance,
proves the Gaussian implication with probability at least one half and
assembles the uniform per-index distance bound.

`BadRowMarkov.lean` proves the actual bad-row expectation and Markov bound
at `ceil(n/d^2)`, without independence between distance events, and obtains
the uniform `2*R/d` failure bound. `RowDeletion.lean` selects exactly `N-t`
surviving rows, preserves their actual distances and proves full row rank.
`RowDistanceDual.lean` constructs geometric biorthogonal duals in the row
span with squared norm equal to inverse squared row distance.
`RowGramInverse.lean` identifies the inverse row Gram with the dual Gram,
including the diagonal and trace distance identities.
`HermitianInverseTrace.lean` checks the general spectral inverse-trace
formula. `RowNegativeSecondMoment.lean` checks the actual Gram equals
`H H*` and uses its ordered eigenvalue square roots as singular values.
It proves the full-row-rank negative second-moment identity for the actual
retained shifted matrix, the source post-deletion sum bound and a closed
uniform event with probability at least `1-2*R/d`.
`SingularValueCounting.lean` proves the inverse-moment tail count and the
actual retained singular-value bounds. The spectral Rayleigh and leading
subspace modules prove eigenvalue comparison through a linear isometry.
`EuclideanCoordinateEmbedding.lean` gives that isometry and the exact
principal-matrix quadratic-form identity; `PrincipalEigenvalueComparison.lean`
therefore proves same-position principal Hermitian eigenvalue comparison.
`RowSingularValueComparison.lean` identifies the actual smaller row Gram
as a principal submatrix and proves singular values increase when rows
are added, including rank-deficient rows.
`IntermediateIndexBounds.lean` now checks all literal source floor/ceiling
indices and `q0<=5*n/d^2<n`, including the exact `t+1` surviving tail.
`SquareSliceSingularValues.lean` identifies singular values of the full
literal shifted square matrix through its nonnegative `A A*` spectrum.
`IntermediateExponentialRadius.lean` absorbs division by the degree into
the exponential scale. `IntermediateSingularValueTheorem.lean` assembles
the full uniform `B/d` failure estimate, and
`FixedShiftIntermediateTheorem.lean` gives every fixed complex shift and
success probability tending to one for every lower-band degree sequence.
Both `thm:intermediate` and its introductory restatement are now proved.
`IntermediateDeletionBudget.lean` proves the exact logarithmic deletion
cost is at most `5*log(d)/d` and tends to zero, supplying that scalar input
to the Section 9 bottom-tail argument.

The Section 8 moment argument now uses the actual independent Bernoulli
product law in `BernoulliCubeLaw.lean`, including parameters zero and one.
`PositiveContractionGeometry.lean` proves the literal quadratic form and
square-root norm identity, `P^2<=P`, and the trace comparison.
`RegularizedDistanceGeometry.lean` realizes the source function as an
augmented Euclidean norm and proves its convexity and one-Lipschitz
constant. `BernoulliQuadraticMoment.lean` checks the exact second moment
`E f^2=D^2`; `RegularizedDistanceMean.lean` proves `mu<=D` and the upper
bound used for all zero-one candidate rows.

`BernoulliMonomialOrthogonality.lean` supplies every centered diagonal and
off-diagonal cancellation under that same product law, including repeated
coordinates and the two orientations of one unordered pair.
`BernoulliQuadraticVariance.lean` proves the exact quadratic variance
formula with coefficient `2*p^2*(1-p)^2` over ordered off-diagonal pairs,
equivalent to the source's coefficient four over unordered pairs. Its
bound is `p(1-p)*tr(P^2)`. `BernoulliLinearVariance.lean` proves the exact
linear variance and bounds it by `4*p(1-p)*q_(P^2)(u0)`.
`RegularizedDistanceFourthMoment.lean` identifies the actual squared
fluctuation with these two terms, yielding `Var(f^2)<=8*D^2` and
`E f^4<=9*D^4` at `D>=1`. `RegularizedDistanceMeanComparison.lean` proves
`D/8<=mu<=D` by the elementary checked inequality
`36*D^2*f^2 <= 216*D^3*f + f^4` and those exact moments. This completes
both mean conclusions without assuming any concentration input.

`BernoulliSliceFibers.lean` identifies the support-size fiber with the
actual row slice, including its cardinality and literal complex row vector.
`BernoulliSliceConditioning.lean` proves the conditional event law and full
conditional measure equality, with no correspondence assumed.
`BinomialStirlingMass.lean` derives effective factorial bounds from
mathlib's checked Stirling development. `BernoulliSliceMassBound.lean`
then proves that the actual conditioning event at `p=d/n` has probability
at least `1/(4*exp(1)^2*sqrt(d))` for every `1<=d<=n`, including the
full-support endpoint. `BernoulliSliceTransfer.lean` gives the resulting
factor `4*exp(1)^2*sqrt(d)` for arbitrary events and actual Euclidean rows.
Its conditional tail corollary is closed by the proved Bernoulli mean
concentration in `RegularizedDistanceConcentration.lean`.

`TalagrandSliceOptimization.lean` proves the scalar interpolation step
with `c=1/64`, the one-coordinate exponential-moment bound and the final
probability absorption used in [Tao's concentration proof](https://terrytao.wordpress.com/2010/01/03/254a-notes-1-concentration-of-measure/).
`TalagrandGeometry.lean` constructs the literal disagreement masks and
proves their hull compact for arbitrary coordinate alphabets, including
infinite ones. Its nearest mask is attained and gives an actual convex
witness within `2*K` times the mask norm. `TalagrandFunctionSeparation.lean`
checks convex Lipschitz sublevel separation. `TalagrandMaskTransport.lean`
allows coordinate maps to merge values while decreasing convex distance.
`TalagrandInductionGeometry.lean` checks the full squared-distance recursion
by lifting slice and projection witnesses and mixing their convex hulls.

`TalagrandFiniteProduct.lean` proves exact finite product disintegration
for arbitrary coordinate probabilities. `TalagrandHolder.lean` proves
weighted Holder including both endpoint weights. These and the checked
scalar optimization complete the full dimension induction in
`TalagrandFiniteMoment.lean`: `E exp(d_c^2/64)<=1/P(A)` for every
positive-mass set. No concentration result is assumed by that theorem.
`TalagrandFiniteConcentration.lean` proves the two-event inequality and
median tail `4*exp(-t^2/256)` for all finite complex product laws.
`TalagrandFiniteMeasure.lean` proves their exact agreement with actual
product measures; `TalagrandFiniteIndependence.lean` obtains the actual
joint product law from independence on arbitrary probability spaces.
Zero-weight outcomes, zero-mass slices and merged coordinate values are
all covered.

`ComplexFiniteApproximation.lean` constructs a common finite alphabet in
the closed complex disk, measurable coordinate labels, and almost-sure
Euclidean approximations which preserve independence. `ConcentrationLimit.lean`
uses Fatou on two copies of the probability space. `GaussianTwoEventLimit.lean`
then uses positive slack to recover closed thresholds, including atoms.
`ConvexProductMedian.lean` proves the full general two-event inequality and
median tail `4*exp(-t^2/256)`.

`GaussianMedianMean.lean` integrates the tail by layer-cake and the checked
half-line Gaussian integral, proving integrability, `E|F-m|<=64*K`, and
`|E F-m|<=64*K`. Recentring at `t>=128` and enlarging the leading constant
below that threshold give the mean tail. `ConvexProductConcentrationProof.lean`
proves the entire target `ConvexProductConcentrationLemma`, with common
absolute constants `c=1/1024` and `C=4*exp(16)`. No imported concentration
result remains assumed.

`FiniteLawMedian.lean` proves median existence for every real function on
a finite probability space, permitting zero-weight outcomes.
`RegularizedDistanceConcentration.lean` applies the full convex theorem to
the actual independent Bernoulli coordinates and closes their mean tail.
Exact conditioning then gives the actual row-slice tail with `sqrt(d)`
loss. Together with the checked mean comparison, this proves the full
`RegularizedDistanceConcentrationLemma` for every `1<=d<=n`, actual positive
contraction, positive regularization and arbitrary complex shift at `D>=1`.
`TruncatedGaussianMoment.lean` bounds the positive excess after a cutoff
which absorbs a Gaussian-tail prefactor. `DistanceLogDegreeMoment.lean`
checks that `256*sqrt(log(e*d))` absorbs the actual slice prefactor, and
layer-cake bounds both absolute first moments by `288*sqrt(log(e*d))`.
`LogComparisonGeometry.lean` proves the good-event logarithmic Lipschitz
bound and the exceptional-event bound `log(U/eta)`.
`LogComparisonExpectation.lean` integrates them for arbitrary joint laws.
`OneRowLogScale.lean` derives `D>=sqrt(Q)` and `mu>=sqrt(Q)/8` from the
literal trace bound. `OneRowLogRates.lean` gives the good rate
`9216*sqrt(log(e*d)/Q)` and exceptional rate `exp(-Q/262144)`.

`FiniteLawTransport.lean` transfers integrals, integrability and events
using the exact finite marginal laws on any probability space.
`OneRowLogComparison.lean` therefore proves the full target
`OneRowLogComparisonLemma`, retaining arbitrary `r<n`, the actual positive
contraction and shift, `Q=p*(1-p)*(r+1)>=1`, and the almost-sure upper bound.
It permits every coupling of the slice and Bernoulli rows; independence
between the two rows is not required. Every moment, tail and mean estimate
is supplied by the checked development.

`HybridRidgeGram.lean` proves positive definiteness of both ridge Gram
matrices and their inverse intertwining identity. `HybridComparisonMatrix.lean`
proves that the actual Schur comparison matrix and its entrywise conjugate
are positive contractions, and that the original matrix fixes the row kernel.
`HybridComparisonTrace.lean` proves the exact trace identity and the
`n-k+1` lower bound. `HybridSchurDeterminant.lean` proves the literal
inserted-row determinant factorization, including the conjugation required
by the complex row convention. `HybridLogPotential.lean` turns that factor
into the exact difference of regularized-distance logarithms.
`HybridOneRowIncrement.lean` supplies every comparison-matrix hypothesis
of the checked one-row theorem and its uniform upper bound
`sqrt(eta^2+(sqrt(n)+R)^2)`, giving the expected potential increment with
the other rows fixed. `HybridRowReindex.lean` isolates any selected row
without changing the potential. `RowHybrid.lean` defines the literal prefix
hybrids and proves that their common other-row matrix is unchanged; its
shift norm bound is the attained maximum of the actual deterministic norms.
`FiniteProductConditioning.lean` splits every finite product law into a
selected coordinate and its complement. `RowHybridExpectation.lean` uses
this identity and the exact slice/Bernoulli pair marginals to bound each
random hybrid increment. `RowReplacementTelescoping.lean` sums these bounds
without independence between increments and checks that `k/n<=1` leaves
the same error rate. `IndependentFiniteFamilies.lean` proves the product
pair law from independence within each family and mutual independence of
the two full families. Exact transport in `RowReplacementTheorem.lean`
therefore proves `GeneralizedRowReplacementProposition` on arbitrary
probability spaces, with all source parameters, shifts, laws and
independence assumptions retained. No hybrid conditioning or telescoping
input remains assumed.

The full Section 9 negative logarithmic tail lemma is now checked.
`LogTruncationGeometry.lean` constructs bounded continuous truncations of
both logarithmic parts, with the negative truncation equal to its threshold
at zero. Its positive truncation excess is at most the squared singular
value divided by the threshold. `LogTruncationIntegrals.lean` proves
integrability of both parts and dominated convergence of the truncations
from the source finite Lebesgue logarithmic integral. That finite-integral
hypothesis is recorded as zero mass at zero and ordinary real-log
integrability off zero; this is its extended-log meaning, not an additional
moment assumption. The proof does not need a second-moment bound for the
limiting measure.

`VaryingProbabilityConvergence.lean` checks limits on sample spaces that
may vary with dimension. `EmpiricalWeakConvergence.lean` retains bounded
continuous test functions and encodes convergence to the finite full-log
limit with the zero event included. `EmpiricalPositiveLogConvergence.lean`
uses the actual tight second moments and positive truncations to prove the
positive-log limit. Exact finite-mean and integral decompositions in
`EmpiricalNegativeLogConvergence.lean` give the total negative-log limit.
`EmpiricalNegativeLogUI.lean` proves the literal iterated limsup tail
conclusion. `BottomLogGeometry.lean` supplies the actual bottom indices,
their cardinality and the threshold bound; `BottomLogConvergence.lean`
proves the consequence for every `r/n->0`.

`NonnegativeEmpiricalMeasure.lean` constructs the source empirical measure,
proves its probability mass and exact real and Lebesgue integral formulas,
and checks that any zero value makes the negative-log tail infinite.
`ExtendedEmpiricalLog.lean` gives the signed integral its minus-infinity
value at zero and checks its finite-neighborhood event encoding. It also
identifies the literal extended bottom sum and its exact infinity event.
`NegativeLogUniformIntegrability.lean` therefore proves the full target
`NegativeLogUniformIntegrabilityLemma` for nonnegative decreasing random
arrays, retaining the source weak convergence, finite logarithmic limit,
tight second moments and both conclusions. No logarithmic truncation or
probability-limit input remains assumed.

`SquareSingularSecondMoment.lean` identifies the sum of squared ordered
singular values with the literal entrywise matrix energy, using checked
Hermitian diagonalization and the Gram trace. It constructs their empirical
probability measure and proves its exact second-moment integral.
`MatrixEnergyShift.lean` checks scalar normalization, diagonal energy and
the shift bound. `BernoulliSquareMatrixLaw.lean` constructs the actual
independent-entry Boolean cube, its matrix and singular measure, and proves
that the total number of ones has mean `n*d` at `p=d/n`. The law is totalized
by clipping the parameter at one in invalid early dimensions; it equals
the source law at every valid dimension. Under `d->infinity` and `d=o(n)`,
all sufficiently large dimensions are proved valid.

`BernoulliSecondMoment.lean` proves the literal second-moment assertion in
part (iii) of `prop:Bernoulli-hermitization`. Its expectation is at most
`2+2*abs(z)^2`, its tail above `M>0` is at most that constant divided by `M`,
and hence it is bounded in probability on the actual varying sample spaces.
This proof holds for every fixed complex shift, including zero.
`BernoulliLogTailReduction.lean` supplies the measurable decreasing singular
array and this tight second moment to the checked logarithmic-tail lemma.
Weak and full logarithmic convergence to a finite logarithmic limiting law
remain explicit arguments of these reductions. Neither the Bernoulli
interface nor its bottom-tail corollary is counted as fully proved.

`MonotonePrefixMean.lean` proves that the full mean of a monotone finite
list dominates every positive integer prefix mean, by a finite double-sum
comparison. `SquareLogPrefixComparison.lean` applies it to the actual
negative singular-value logarithms and proves the exact lower comparison
`U >= (n/ell)*T1` when the singular values are positive. Singular samples
retain their extended values in the earlier logarithmic definitions. The
upper squeeze remains a mathematical proof obligation. Bernoulli weak-law
transfer and Gaussian logarithmic-potential identification are proved below.

`SmallValueLogIntegrability.lean` proves the analytic finiteness implication
from Fact 10.1's stated properties. For any finite measure with
`nu([0,t))<=C*t` for every positive `t`, the mass at zero vanishes.
The closed negative-log tail is at most `C*exp(-u/2)`; layer-cake integration
gives an integrable negative logarithm with integral at most `2*C`.
Bounded support gives an integrable positive logarithm, hence the exact
`FiniteLogarithmicIntegral` required by the full logarithmic-tail lemma.
Existence, Gaussian convergence and the actual bounds of that limiting
measure are now proved below. Transfer to the Bernoulli singular array
remains open. The Gaussian circular-potential identity is proved below.

`SpectralCodimensionComparison.lean` proves the lower spectral comparison
under an isometry with index loss equal to its codimension, by intersecting
the ambient leading spectral subspace with the isometry's range. A second
comparison intersects with a linear-map kernel and loses at most the
codomain dimension. `PrincipalEigenvalueInterlacing.lean` supplies both
sides of Cauchy interlacing for the actual principal quadratic form.
`RectangularSingularInterlacing.lean` applies them to arbitrary rectangular
matrices and actual row restrictions, giving the exact number-of-deleted-rows
singular-value shift. No rank, shift or random-matrix assumption is needed.
`MatrixColumnRestriction.lean` identifies the actual erased-coordinate
map, its codomain dimension, quadratic domination and quadratic equality
on its kernel. `ColumnSingularInterlacing.lean` applies the spectral kernel
comparison to prove both column-deletion bounds.
`PrincipalSingularInterlacing.lean` combines the row and column applications
to prove the exact `2*(n-m)` shift for any square principal submatrix.

`ExactMinorLogComparison.lean` proves a compatible finite upper logarithmic
comparison, using the half-open ambient interval `[2*(n-m),m)` and its
exact cardinality `k=m-2*(n-m)`. The remaining `ell-k` prefix terms are
bounded by the last retained minor logarithm. It assumes `2*(n-m)<=m`,
`k<=ell<=m`, `ell>0`, positive ambient singular values and positive minor
singular values only in the retained prefix. Negative logarithms may have
either sign. The corrected deterministic finite comparison is checked;
the probabilistic squeeze and its truncation and rounding limits remain
obligations.

The exact rounded upper comparison `eq:SSS-T-upper` is now a verified
statement-review issue. `ScalarSquareSingularValues.lean` identifies every
singular value of a scalar identity matrix through its actual Gram
eigenvectors. `RoundedMinorLogReview.lean` checks all five manuscript
rounded parameters at `n=100`, `epsilon=1/10` and proves that `H=2I` gives
`T=-(87/100)*log(2)` but `T2=-(88/100)*log(2)`, so `T<=T2` fails.
`BernoulliEmptyMatrix.lean` checks that this is the actual shifted
Bernoulli matrix with `B=0` and `z=-2`, and that this sample has strictly
positive probability at `p=d/n=1/10`. The [review note](HERMITIZATION_REVIEW.md)
records the required integer-bookkeeping revision. Manuscript sources
are unchanged, and neither a corrected probabilistic squeeze nor the full Bernoulli
logarithmic convergence assertion is counted as proved.

The current checked foundations and the twenty-one completed manuscript result entries
are listed in [README.md](README.md). The machine-readable coverage of
all named manuscript results is in [paper-coverage.json](paper-coverage.json).

`SmallValueCutoff.lean` constructs a bounded continuous cutoff that equals
one below `a` and zero above `b>a`. Its integral is at most the limiting
mass below `b`. Its empirical mean dominates the exact tail fraction when
any retained ordered value is below `a`. `RetainedPrefixSmallValues.lean`
therefore proves that a prefix omitting at least a fixed fraction `eta`
has no value below `eta/(4*C)`, with probability tending to one, under weak
convergence and the limiting bound `nu([0,t))<=C*t`. Discarded zero values
are permitted; no full logarithmic convergence is used as an input.

`BernoulliSqueezeRounding.lean` retains both literal manuscript floors.
It proves that the removed prefix fraction is at least `epsilon` for
`0<=epsilon<=1`, that `m/n`, `ell/n` and `n/ell` tend to one, and that both
removed fractions tend to zero for nonnegative `epsilon_n->0`.
The exact correction's base count is at most `ell`, and its deleted-column
and deleted-row shift eventually fits inside `m`. Thus the finite corrected
comparison's integer conditions are supplied by checked arithmetic.

`VaryingProbabilityTransfer.lean` transfers probability convergence through
an eventual uniform error tending to zero. `EmpiricalPrefixMeans.lean`
defines the actual prefix sum divided by `n`, identifies its exact indices
and bounds its difference from a full bounded-test mean by the omitted
fraction times the test bound. It proves convergence for all fixed bounded
continuous tests, including both fixed clipped logarithms, and identifies
the untruncated negative prefix with its clipped version on the explicit
no-small-prefix event.

`BernoulliPrefixConvergence.lean` applies these deductions to the actual
Bernoulli matrix law and the exact manuscript prefix. It proves the fixed
`epsilon` retained-value bound, fixed negative-clipped convergence when
`epsilon_n->0`, and the identity with the literal square negative-log
prefix. Bernoulli weak convergence to the Gaussian law and the limiting
mass bound are explicit arguments of these reductions. The full
untruncated `T1` deduction is supplied below. The actual Gaussian weak law
and mass bound are now proved. Bernoulli weak-law transfer and common literal
minor `T` convergence are proved below. The actual full-to-minor upper estimate
remains an obligation; the named Bernoulli interface is still partial.

`SlowDiagonal.lean` constructs increasing integer thresholds and a
monotone stage selector tending to infinity. Any fixed stage's eventual
estimate holds at the selected stage and current dimension.
`LogarithmicStages.lean` uses integer cutoffs `T_k=k+K` and positive
fractions `epsilon_k=4*C*exp(-T_k)`. A checked offset gives `epsilon_k<=1`;
both `epsilon_k` and `epsilon_k*T_k` tend to zero.
`SqueezeRoundingError.lean` supplies the exact bound on the omitted source
prefix fraction, `5*epsilon/4+2/n`.

`PrefixNegativeDeviation.lean` proves the untruncated negative-prefix
deviation bound on the no-small event, keeping the complementary event
and retained zeros explicit. `RoundedNegativePrefixConvergence.lean`
chooses the stage slowly enough that the small-value probability, clipped
deviation probability and finite rounding error are all small at once.
The full untruncated negative prefix converges to the limiting negative
logarithmic integral, and retained zeros have vanishing probability. It
uses weak convergence, the limiting linear mass bound and a finite
limiting logarithmic integral; empirical full-log convergence is not an
assumption of this proof.

`EmpiricalPositivePrefixConvergence.lean` controls the full-to-prefix
positive-log difference by the clipped omitted fraction plus the full
clipping excess. Tight second moments make this difference vanish in
probability, even for unordered arrays. `RoundedLogPrefixConvergence.lean`
combines both parts along the same stage selector to prove the complete
signed prefix potential limit.

`BernoulliSlowPrefixLimit.lean` supplies the actual Bernoulli tight second
moment, derives limiting logarithmic finiteness from the mass and support
bounds, and identifies the resulting sum with the literal two-floor `T1`.
It constructs a positive nonincreasing `epsilon_n->0` and proves
`T1 -> -integral(log,nu)` with retained-zero probability tending to zero.
Bernoulli weak convergence and limiting mass/support bounds are explicit
arguments of this deduction. The Gaussian weak law, support and linear
small-value mass bounds are proved below at every shift. Transfer to the
Bernoulli array is also proved below. The Gaussian circular-potential identity
is proved below. The
corrected upper quantity `T2` and actual full-to-minor upper estimates remain
open, so the named interface is still partial.

The negative, signed and actual Bernoulli slow-prefix theorems now preserve
arbitrary additional fixed-stage eventual constraints. `SlowProbabilityLimits.lean`
proves that a stage-dependent random variable converges along the selector
when its selected-stage deviation probability is bounded by the vanishing
diagonal accuracy and its stage limits converge. `BernoulliJointPrefixLimit.lean`
uses this to supply a common choice for `T1` and an auxiliary quantity, with
the auxiliary fixed-fraction probability limits kept as explicit inputs.

`VaryingProbabilitySqueeze.lean` proves deterministic normalization transfer,
agreement outside a vanishing bad event, and an asymptotic squeeze that also
proves the bad-event probability tends to zero. `BernoulliLogSqueeze.lean`
applies it to the actual full Bernoulli negative-log mean, literal rounded
ambient and minor prefixes, and singular samples. The source lower comparison
and `n/ell->1` are supplied by checked proofs. Minor-prefix convergence and
the full-to-minor upper failure probabilities remain explicit inputs.

`BernoulliSlowLogSqueeze.lean` supplies the entire common slow-choice assembly
from fixed-fraction inputs. It requires actual minor-prefix probability limits
`a(epsilon)`, their limit `-integral(log,nu)` as `epsilon->0+`, and actual
upper failure probabilities with error `e(epsilon)->0`. The fixed-fraction
inputs need only hold in some positive neighborhood of zero. One selector
enforces both sets of deviation bounds together with the actual `T1` bounds.
It gives `EmpiricalLogConvergenceInProbability`, including vanishing zero
probability. Bernoulli weak-law transfer and Gaussian/circular logarithmic
identification are proved below. Actual minor-prefix fixed-fraction limits
and actual upper estimates are supplied by the actual greedy process below.

`SquareSingularDeterminant.lean` proves that the product of the actual ordered
singular values equals the absolute determinant, using the Gram determinant
and its eigenvalues. A zero singular value is equivalent to a zero determinant.
On the nonsingular event the logarithmic sum equals the log absolute determinant.
`BernoulliLogDeterminant.lean` consequently transfers the full empirical log
limit to the actual normalized log determinant and proves vanishing singular
probability. The probability limit survives arbitrary redefinition on the
singular event. Actual full Bernoulli log convergence remains an input here.

The deterministic ESD normalization transfer in both circular-law regimes
is now complete. `UnitaryMatrixEnergy.lean` proves invariance of the actual
entrywise energy and characteristic polynomial under unitary conjugation.
`UnitaryEigenvectorReduction.lean` constructs a normalized eigenvector and
an orthonormal basis with that vector first. The transformed matrix has a
first column containing only its eigenvalue. `SchurBlockReduction.lean`
factors the characteristic polynomial into that eigenvalue and the actual
remaining block, and bounds their combined energy by the original energy.
Dimension induction in `SchurEigenvalueEnergy.lean` gives the full Schur
bound on the squared norms of all characteristic roots, with algebraic
multiplicities retained and no diagonalizability assumption.

`EigenvalueFirstMoment.lean` applies Cauchy-Schwarz to a full enumeration
of the characteristic-root multiset, giving a first eigenvalue moment at
most `sqrt(squareMatrixEnergy(A)/n)`. `CharacteristicRootScaling.lean`
proves exact scaling of the root multiset for every complex scalar,
including zero. `EmpiricalSpectralIntegrals.lean` supplies the literal
finite Dirac integrals. `SpectralRescalingBound.lean` proves the full
bounded-Lipschitz triangle inequality and the deterministic bound
`d_BL(mu_(c*A),mu_A)<=norm(c-1)*sqrt(energy(A)/n)`.

`VarianceNormalizationTransfer.lean` applies this to actual row slices.
At `sqrt(d)` normalization the energy per dimension is exactly one; the
variance-normalized matrix is exactly `(1-d/n)^(-1/2)` times that matrix.
The ESD distance is at most `abs((1-d/n)^(-1/2)-1)`, which tends to zero
for every sparse degree sequence. This bound holds uniformly for all
samples. Probability convergence transfers under arbitrary degree-regime
filters, and both degree-normalized regime tail bounds feed the actual
main-target assembly. The regime circular-law estimates themselves are
still unproved. This transfer supplies their normalization step, not their
actual logarithmic-comparison or sparse i.i.d. circular-law inputs.

The deterministic potential inputs of the replacement principle now have
checked proofs. `CharacteristicRootShift.lean` transports every root,
with algebraic multiplicity, under scalar subtraction and identifies the
actual ESD atoms. `SpectralLogPotential.lean` proves the actual ESD log
potential equals the normalized shifted log determinant away from its
finite eigenvalue set, which has area zero. Their extended values agree
at every shift, with minus infinity at each singular shift, and equal the
extended logarithm of the actual ordered singular values.
`SpectralLogConvergence.lean` transfers full singular-log convergence to
the actual spectral potential; the limiting convergence remains an input.

`PlanarLogIntegrability.lean` and `PlanarSquaredLog.lean` use the planar
polar area factor to prove local absolute and square integrability,
including near every eigenvalue. Jensen bounds the squared actual ESD
potential by the mean of its squared logarithmic kernels. In
`SpectralLogSquareBound.lean`, the near-zero kernel has spatial square
integral at most `32*pi`, uniformly under translation. On a disk of radius
`R`, the full potential's square integral is at most
`32*pi + 2*area(disk)*(R^2+energy(A)/n)`. The actual shifted log determinant
has the same integral and is also locally square integrable. Actual
`B/sqrt(d)` row slices therefore have a uniform spatial L2 bound; actual
Bernoulli matrices have this spatial square integral bounded in probability.

`SpectralEnergyTightness.lean` gives the actual ESD second moment at most
`energy(A)/n` and radial tail at most `energy(A)/(n*R^2)`. This proves
uniform spectral tightness for degree-normalized row slices and tightness
in probability for the actual sparse Bernoulli law. No circular-law limit
is used in these inputs.

The spatial probability-to-integral passage is now proved in
`SpatialSquareGeometry.lean`, `SpatialBadArea.lean` and
`SpatialProbabilityConvergence.lean`. Actual Fubini identifies expected
bad-set area with the spatial integral of pointwise event probabilities.
Dominated convergence and Markov make that bad area vanish in probability.
A square-integral split then gives spatial L1 convergence from spatial
L2 bounds in probability, on varying sample spaces. Bounded test integrals
converge in probability as well.

`VaryingProbabilityBounded.lean` checks the probability-bound arithmetic.
`LogDeterminantSpatialConvergence.lean` supplies the canonical Borel matrix
space and joint measurability of the actual shifted log determinant. The
normalized energy bounds give the spatial squared-difference bound, so
almost-everywhere pointwise log-difference convergence gives spatial L1
convergence on every disk. Compactly supported bounded tests give the
whole-plane integral convergence of both actual log determinants and ESD
logarithmic potentials. The actual pointwise logarithmic limit is still
an explicit hypothesis; no circular-law limit is assumed to derive the
spatial passage.

The distributional logarithmic-kernel identity is now proved.
`PlanarLogApproximateIdentity.lean` checks the actual planar kernel
`1/(pi*(1+norm(z)^2)^2)`, its mass one and its approximate-identity limit.
`SmoothedPlanarLog.lean` computes actual real Fréchet derivatives of
`log(norm(z)^2+epsilon^2)/2` and mathlib's Laplacian, which equals
`2*epsilon^2/(norm(z)^2+epsilon^2)^2`. Its integral against an integrable
test continuous at zero tends to `2*pi` times that test's value at zero.

`PlanarGreenIdentity.lean` proves Green's identity for every compactly
supported C2 test and arbitrary C2 weight, discharging both integrations
by parts and their integrability obligations. In
`PlanarLogFundamentalSolution.lean`, an actual integrable logarithmic
majorant gives dominated convergence at the singularity. Translation
then gives, at every `w`,
`integral(log(norm(z-w))*Laplacian(phi)(z)) = 2*pi*phi(w)`.
`SpectralLogReconstruction.lean` sums over the actual characteristic roots,
retaining algebraic multiplicity, and reconstructs actual ESD test integrals
from both the ESD potential and shifted log determinant. Combining this
identity with the spatial probability passage proves convergence of every
compactly supported C2 eigenvalue test integral under the actual energy
and almost-everywhere logarithmic hypotheses.

The full extension to bounded-Lipschitz distance is now proved in
`BLCompactSmoothApproximation.lean`, `BLFiniteApproximation.lean`,
`BLFiniteSmoothFamily.lean`, `BLIntegralApproximation.lean`,
`BLFiniteSpectralBound.lean`, `VaryingFiniteTestProbability.lean` and
`BLProbabilityConvergence.lean`. Arzela--Ascoli gives compact closure of
the actual restricted BL family. A finite cover chooses centers from
this family, so their global bound one and Lipschitz constant one remain
available. Uniform smoothing and a disk cutoff give a finite compact C2
family, globally bounded by two. The integral approximation error is at
most the disk error plus three times the actual outer spectral mass.
Energy bounds control both tails, and a finite union of test events gives
the required probability bound for the full BL supremum.

`ReplacementPrinciple.lean` assembles the actual measurable matrix,
energy and almost-everywhere log-difference hypotheses into full
BL-distance convergence in probability. It also checks the combined
Hilbert--Schmidt hypothesis and the classical `1/sqrt(n)` normalization:
energy per normalized dimension equals the raw matrix energy divided by
`n^2`. This proves the probability version of Tao--Vu Theorem 2.1 used
throughout this manuscript, by its Section 3.6 distributional route.
The source's additional almost-sure version is outside the paper's stated
probability convergence requirement. `ReplacementLimitTransfer.lean`
checks transfer of any actual comparator spectral limit, including the
circular measure, under these replacement hypotheses. Both actual regime
circular-law estimates and their remaining comparator and logarithmic
inputs remain unproved.

The circular-measure side of the logarithmic-potential identity is now
proved in `CircularPotentialPolar.lean`, `RadialCircularPotential.lean`
and `CircularLogPotential.lean`. The actual uniform unit-disk integral
is `(norm(z)^2-1)/2` inside the disk and `log(norm(z))` outside,
including the origin and unit-circle boundary. The paper's `U^circ`
is its negative. Polar Fubini integrability, the singular angular
average, the radial primitive at zero, continuity and spatial square
bounds are all checked. This does not identify the actual Gaussian
limiting singular law or its logarithmic integral; that source input
remains unproved.

`CircularLogReconstruction.lean` proves joint integrability of the
actual logarithmic kernel against every compact continuous test, using
uniform section bounds over the unit disk. Fubini and the checked
fundamental solution reconstruct the actual circular measure with the
exact `2*pi` Laplacian-test factor. `CircularSpatialConvergence.lean`
applies energy-derived spatial square control to the difference between
actual log determinants and this target potential. `BLCircularConvergence.lean`
constructs a finite smooth cover and uses the target's zero outer mass
to pass from compact C2 tests to the full BL supremum.
`CircularHermitization.lean` therefore proves a direct circular-law
hermitization criterion, in both logarithmic sign conventions, with
measurable matrix families, energy bounded in probability and actual
almost-everywhere logarithmic convergence as its hypotheses. No
comparator ESD convergence is assumed in this direct criterion. The
actual Bernoulli/row-slice logarithmic limits, Gaussian potential identification and
remaining named circular-law results remain proof obligations.

`ComplexGaussianMoments.lean` proves integrability of every polynomial
moment under the actual standard complex Gaussian law. Its radial density
and the Gamma integral give `E(norm(Z)^(2*k)) = k!`.
`ComplexGaussianRotation.lean` proves invariance under every unit complex
multiplier and uses an explicit rotation to cancel unequal powers.
Consequently `E(Z^p * conjugate(Z)^q)` is `p!` when `p=q` and zero
otherwise, including the zero-power cases.

`GaussianEntryProducts.lean` constructs the actual finite product law,
checks its Gaussian marginals and coordinate independence, and applies
Fubini to arbitrary products. Entry words are grouped by their exact
list multiplicities, so repeated matrix-entry indices are retained.
Their expectations vanish unless every coordinate has matching direct
and conjugate multiplicities, and otherwise equal the product of the
multiplicity factorials. The norm is bounded by the direct word-length
factorial, and different direct and conjugate lengths imply zero
expectation. These are checked scalar and independent-entry inputs to
the trace-moment argument. The finite polynomial expansions described
below are checked. Limiting moment combinatorics, concentration, the
actual shifted Gaussian singular-value limit and identification of its
logarithmic integral are now all proved below.

`GaussianWickFour.lean` proves the exact four-entry expectation as the
sum of the two possible direct-to-conjugate pairings. Coincident indices
are retained: the intersection contributes twice, giving fourth moment
two. `GaussianCoordinateMoments.lean` checks evaluation integrability,
coordinate means and affine-coordinate energy means under the actual
product law. `GaussianLinearSecondMoment.lean` proves exact Kronecker
covariance and mean-square norm equal to the coefficient square sum for
every deterministic complex linear form.

`GaussianSquareMatrixLaw.lean` defines the actual iid variance-one
complex Gaussian matrix on ordered entry samples, checks measurability,
entry marginals and independence, and defines its normalized shifted
matrix and actual singular measure. The shifted singular second-moment
mean is exactly `1+norm(z)^2` at every positive dimension.
`GaussianGramTraceMoments.lean` expands the actual second Gram trace over
four ordered indices and sums both checked pairings. Its expectation is
exactly `2*n^3`, including their intersection. `SquareSingularTraceMoments.lean`
uses the actual Hermitian spectral theorem to prove, at every natural
power `k`, that the empirical singular moment of order `2*k` equals the
real trace of the Gram matrix to power `k`, divided by the dimension.

`GaussianSingularMoments.lean` checks arbitrary scalar Gram-trace scaling,
the actual shifted second-moment Markov bound and boundedness in
probability, and exact zero-shift normalized fourth-moment expectation
two. `GaussianProductEnergy.lean` proves mean `N`, square mean `N^2+N`
and centered square mean `N` for the actual energy of `N` independent
coordinates. `GaussianEnergyConvergence.lean` specializes to the matrix's
`n*n` entries: energy divided by `n^2` has centered square mean `1/n^2`,
so its deviation probability is at most `1/(n^2*epsilon^2)` and tends to
zero. The zero-shift empirical singular second moment therefore
converges to one in probability under the actual matrix laws. Higher
trace-moment convergence, shifted weak convergence, the limiting
singular-law bounds and its logarithmic potential identification are
proved below. These low-order calculations alone do not establish that weak limit.

`MatrixEnergyShiftIdentity.lean` proves the exact deterministic shift
identity, retaining the real trace cross term. `GaussianShiftedSecondMoment.lean`
represents the normalized cross term as an actual diagonal Gaussian linear
form. Its norm-square mean is `norm(z)^2`; the trace correction has square
mean at most `4*norm(z)^2/n^2` and deviation probability at most
`4*norm(z)^2/(n^2*epsilon^2)`. The correction tends to zero in probability.
Together with the proved raw energy convergence this gives convergence
of the actual empirical singular second moment to `1+norm(z)^2` for every
fixed complex shift.

`GaussianPolynomialMoments.lean` introduces entry variables with separate
direct and conjugate tags, and expands evaluation over the actual finite
polynomial support. All exponents and coefficient values are retained;
the previously proved entry moment formula gives the exact finite
expectation. `GaussianPolynomialSquareMoments.lean` conjugates coefficients
and exchanges variable tags, proving that this polynomial evaluates to
the actual conjugate. Every norm power is integrable, and the exact
mean-square norm is the real part of the same expectation functional
applied to the polynomial times its conjugate.

`GaussianTracePolynomials.lean` defines the actual normalized shifted
matrix and adjoint as symbolic entry matrices and checks their evaluation.
Evaluation commutes with matrix multiplication, every Gram power and the
trace. Consequently every shifted Gram trace has a checked finite
expectation formula, every even empirical shifted singular moment is
integrable with that normalized mean, and every centered trace square
has an exact finite polynomial expectation. These identities hold at
all natural orders and all dimensions. They do not prove the asymptotic
values of the means or decay of the centered square expectations.

`GaussianPolynomialImbalance.lean` gives direct variables integer weight
one and conjugate variables minus one. Every balanced exponent has weight
zero, so a polynomial homogeneous at nonzero imbalance has exactly zero
expectation under the actual product law. `GaussianMatrixWords.lean`
retains arbitrary noncommuting direct/adjoint word order and checks that
its symbolic trace evaluates to the actual matrix product trace. Its
weighted degree is the direct count minus the adjoint count. Thus every
unbalanced word trace is integrable and has zero expectation at every
dimension. `GaussianScaledMatrixWords.lean` checks the actual scalar and
conjugate scalar factors after arbitrary complex normalization and
preserves the same cancellation. Balanced word counts, their asymptotic
contributions and concentration, the full shifted weak singular limit,
its support and mass bounds, and logarithmic potential identification
are now proved below.

`MatrixGramShiftTrace.lean` checks that Hermitian power traces are real,
that the Gram trace equals actual matrix energy, and the complex trace
scaling identity at every power. Its shifted Gram-square expansion uses
only cyclicity of the trace to group cross terms, retaining all direct
and adjoint words. `GaussianScaledGramMoments.lean` gives the actual
scaled first and second Gram-trace means `norm(c)^2*n^2` and
`2*norm(c)^4*n^3`. `GaussianShiftedFourthMoment.lean` integrates the exact
shift expansion: all six unbalanced words have zero mean, so the actual
shifted fourth singular moment has mean `2+4*norm(z)^2+norm(z)^4` for every
positive dimension. This is an expectation identity; its convergence in
probability is now proved below.

`GaussianPairingCount.lean` constructs the equivalence between matching
permutations and the stabilizer of the direct entry labels when all
fiber counts agree. Otherwise no matching exists. Their exact count is
the product of the fiber factorials. `GaussianWickPairings.lean` combines
this count with the actual Gaussian entry-word integral to prove Wick's
formula at every finite order: the expectation is the sum over all
permutations of products of entry-equality indicators. Coincident labels
retain each matching, and the expectation norm is at most the order's
factorial.

`MatrixGramWalks.lean` expands arbitrary matrix powers as finite entry
paths and every positive Gram power as closed row and column walks.
`GaussianGramTracePairings.lean` checks integrability of each actual walk,
integrates its entries using Wick's formula, and retains the complete
row and column equality constraints for every matching permutation.
The normalized zero-shift singular moment has the same finite sum
divided by `n^(k+2)` at Gram power `k+1`.

`PermutationCycleColorings.lean` uses the actual permutation same-cycle
quotient, including fixed points. Every invariant assignment descends
to a quotient coloring and conversely, so a permutation with `c` cycles
has exactly `n^c` assignments to `Fin n`. `GaussianPairingCycleCounts.lean`
reduces the row constraints to invariance under the cyclic successor
composed with the inverse matching, and the column constraints to
invariance under the matching itself. Thus the actual raw Gram-trace
mean at power `k+1` is exactly the sum over all matching permutations
of `n^(cycles(sigma)+cycles(rotate*sigma^-1))`. The real trace mean and
normalized singular-moment formula are checked too. These are finite
identities, including nonleading terms. Their exponent bound, mean limits
and concentration are now proved below. The full shifted weak singular
limit, support and mass bounds, and zero-shift Catalan enumeration are also
proved below. Shifted logarithmic-potential identification is also proved below.

`FiniteIncidenceGraph.lean` represents actual labels as edges between
the two cycle-class vertex types. Every graph edge comes from a label,
so a connected graph has at most `card(labels)+1` vertices, using the
checked spanning-tree cardinality bound. `PermutationCycleGraph.lean`
proves reachability along the product of the two permutations and their
integer powers. The cyclic successor makes the one-trace graph connected.
`GaussianMomentCycleBound.lean` therefore proves the exponent bound
`cycles(sigma)+cycles(rotate*sigma^-1)<=k+2` at Gram power `k+1`.

`DimensionPowerLimit.lean` proves the limits of `n^d/n^m` when `d<=m`,
including exact inverse-power expressions and bounds by one and `1/n`.
`GaussianMomentMeanLimits.lean` applies them to the actual zero-shift
singular-moment expectation. Every fixed positive even order has mean
between zero and its order factorial at positive dimension. Its limit
is the exact number of permutations attaining the maximal exponent.
`GaussianZeroCatalanMoments.lean` now identifies these limiting counts with
the corresponding Catalan numbers, as detailed below.

`GaussianTwoTraceCycleBound.lean` uses the successor on `Bool` times
the positions within one trace. Its orbits are the two trace blocks.
A matching crossing the blocks identifies their cycle vertices and
makes the graph connected. The total exponent is then at most
`2*(k+1)+1`, below the normalization `2*(k+1)+2`.
`GaussianMixedPairingDecay.lean` bounds the complete crossing contribution
by `(2*(k+1))!/n` and proves that it tends to zero.

`GaussianFinitePairings.lean` transports Wick matching to arbitrary
finite position types by conjugating the actual matching permutations.
`MatrixGramTraceProducts.lean` gives an exact square-of-trace expansion
over both blocks. `GaussianTwoTracePairings.lean` checks its integrability
under the actual Gaussian matrix law, then integrates every joint walk.
The complex and real second moments are exactly the full two-block
cycle sum; Hermitian traces are real, so this is the actual real square.

`BlockPreservingPermutations.lean` constructs the equivalence between
block-preserving permutations and independent within-block permutations.
Their invariant colorings split over the blocks. Counting binary
colorings, then using injectivity of powers of two, proves additivity of
the actual cycle counts, including fixed points. `GaussianSeparatePairings.lean`
uses this equivalence to show that the separate-pairing sum is exactly
the squared one-trace sum. `GaussianMomentVariance.lean` identifies
the normalized even singular moment with the raw Gram trace divided by
`n^(k+2)`. Its centered square expectation is exactly the crossing
contribution, hence at most `(2*(k+1))!/n` for positive dimension.

`VaryingMeanSquareConvergence.lean` checks the actual-event Markov bound
and the implication from a vanishing mean-square error to convergence
in probability on varying sample spaces. `GaussianMomentConvergence.lean`
combines the all-order mean limits and variances: the square error around
each limiting leading count tends to zero, and every fixed positive even
zero-shift singular moment converges to that count in probability. The
already checked fourth-moment mean identifies its leading count as two,
giving explicit fourth-moment convergence to two. Higher shifted moments
and the weak law at general shifts are now proved below. Logarithmic
identification remains a proof obligation. The linear mass bound now follows from actual Gaussian
quantile estimates for every weak limiting probability law, as detailed below.

`GaussianLeadingTrees.lean` identifies the objects in the limiting
counts more precisely. The one-trace graph is always connected. A
maximal exponent forces exactly one edge per actual position and one
more vertex than edges, hence a tree with bijective position-to-edge
map. Conversely, that tree and bijectivity force the maximal exponent.
This is a checked characterization of every leading pairing. The exact
first-pair decomposition and its Catalan recurrence supply the enumeration
below; the tree characterization alone does not supply that count.

`ComplexLatticeNet.lean` constructs a complex half-net from two actual real
quarter-nets. It covers the complex unit ball, its points have norm at most
two, and its cardinality is at most `128^(2*n)<=exp(14*n)`.
`ComplexHalfNetReduction.lean` checks vector and operator approximation:
control of every inner product on two such nets gives an operator bound
with factor four.

`GaussianLinearFormLaw.lean` identifies the distribution of every finite
complex linear form under the actual independent-entry law. Its scale is
the square root of its coefficient energy, including the degenerate zero
case. `GaussianLinearFormTails.lean` derives radial probability bounds from
this exact law. `GaussianMatrixBilinearTail.lean` identifies a matrix inner
product with this linear form and proves coefficient energy
`norm(u)^2*norm(v)^2`. Net points therefore give tail `exp(-(r/4)^2)`.

`GaussianMatrixNorm.lean` applies the finite union bound to all actual net
pairs. Choosing `r=32*sqrt(n)` gives an operator norm at most `128*sqrt(n)`
with failure probability at most `exp(-36*n)` at every positive dimension.
`ComplexMatrixOperatorBounds.lean` checks complex scaling, subtraction,
adjoints and the bound of every actual ordered singular value by this
operator norm. `GaussianShiftedNormSupport.lean` applies the literal
`1/sqrt(n)` normalization and shift: all singular values are at most
`128+norm(z)` with the same exponential failure bound.

`VaryingProbabilityUnique.lean` proves uniqueness of deterministic limits
in probability on varying sample spaces. `GaussianWeakLimitSupport.lean`
uses the matrix estimate to show that every bounded continuous test
vanishing below `128+norm(z)` has empirical mean tending to zero in
probability. If the actual shifted empirical laws converge weakly in
probability to a finite measure, each such limiting integral is zero.
A positive continuous cutoff then proves that the limiting measure has
no mass above this radius. This support implication is fully checked;
existence of the shifted weak limit and its logarithmic-potential
identification remain proof obligations. Linear small-value mass inheritance
is now proved below for any actual weak limiting probability measure.

`VaryingProbabilityPolynomial.lean` proves addition, finite sums and
polynomial empirical-test convergence on varying probability spaces.
Every polynomial test is the exact finite combination of the actual
empirical moments. `VaryingMomentSamples.lean` combines their fixed finite
deviation events with the upper-bound failure event. The union eventually
has probability less than one, giving samples within the bound whose
first `k+1` moments all have error at most `1/(k+1)`.

`CompactMomentExistence.lean` puts these actual samples into finite uniform
probability measures on `[0,R]`. Compactness of the interval's probability
measure space yields a weakly convergent subsequence, and every continuous
power test has the prescribed limiting integral. `CompactMomentConvergence.lean`
then uses Weierstrass approximation for each continuous interval test.
Outside the upper-bound failure event, the polynomial controls both the
empirical test and its limiting integral, proving the actual test limit
in probability. Neither existence nor weak convergence is an assumed
conclusion of this construction.

`GaussianSquaredMomentLimits.lean` connects every squared singular moment
to the previously proved even Gaussian moments, including the zeroth
moment one. The actual Gaussian bound makes the probability that any
squared singular value exceeds `128^2` tend to zero.
`GaussianZeroWeakLimit.lean` applies the compact construction to obtain
an actual limiting probability measure on `[0,128^2]` with all these
moments. Its nonnegative square-root pushforward is the limiting law of
the actual zero-shift Gaussian singular values. Every bounded continuous
test converges in probability, and all even limiting moments are the
exact leading pairing counts. Support in `[0,128]` is checked.

`EmpiricalWeakLimitUnique.lean` uses uniqueness of deterministic probability
limits and determination of finite Borel measures by bounded continuous
test integrals to prove uniqueness of actual weak limits.
`GaussianZeroLimitProperties.lean` applies it to the constructed law.
Comparison with the actual energy limit identifies the second leading
count as one; the limiting second and fourth moments are one and two.
The actual zero-shift weak law is now proved. Its Catalan moments and the
weak law at general shifts are proved below. The explicit transformed-beta
law, sharp support in `[0,2]`, quarter-circle density form and logarithmic
value `-1/2` are also identified below. The constructed zero-shift law now has
the linear small-value mass bound and a finite logarithmic integral, as
detailed below.

`ComplexGaussianShiftLaplace.lean` completes the square in the actual
complex Gaussian density and integrates its translated planar Gaussian.
`GaussianShiftNormLaplace.lean` factors the finite coordinate product:
the negative-exponential integral is exactly
`(1+a)^(-n)*exp(-a/(1+a)*norm(w)^2)` for `a>=0`. Markov then gives the
uniform shifted-vector small-ball bound `(exp(1)*u/n)^n` for positive
dimension and threshold.

`GaussianShiftProjectionNorm.lean` uses the checked Gaussian isometry law
to transfer this calculation to any actual subspace of rank `p>0`.
Squared projected norm at most `p/8` has probability at most `2^(-p)`,
uniformly in the deterministic shift. `FiniteSpanDistanceMeasurable.lean`
expresses distance to a finite span as the infimum over its coefficient
combinations. This proves upper semicontinuity and measurability for
continuously varying vectors and rows, including at rank changes.

`GaussianShiftSpanDistance.lean` identifies that distance with the
orthogonal projection norm. The complement's rank is at least the ambient
dimension minus the number of rows; the small-ball bounds also imply zero
probability of membership in a proper finite span.
`GaussianIndependentSpanDistance.lean` checks the joint distance event's
measurability and applies Fubini. For an independent fresh shifted Gaussian
vector after conditioning on continuously varying rows, squared distance
at most `(n-card(rows))/8` has probability at most
`2^(-(n-card(rows)))`, and distance is almost surely positive.

`GaussianProductCurry.lean` verifies every measurable product rectangle
to identify the uncurried product of row laws with the actual product law
on matrix entries. The singular-value counting application and limiting
linear small-value mass bound and general shifted weak law are now
proved below. The Gaussian/circular logarithmic identity is also proved below.

`GaussianRowExposure.lean` splits any selected actual row into the other
rows and an independent fresh vector by a measure-preserving map. A
finite union bounds all leave-one-out distance failures. Their almost
sure positivity proves linear independence of every shifted rectangular
row family with no more rows than columns. `GaussianShiftFullRank.lean`
uses the exact uncurrying law and the finite basis determinant criterion:
the actual normalized shifted square matrix has nonzero determinant and
positive singular values almost surely at every positive dimension.

`GaussianConjugateLaw.lean` checks scalar conjugation invariance by
characteristic functions, then checks every finite product pushforward.
`FiniteRowDistanceDual.lean` constructs geometric duals for arbitrary
rows and proves biorthogonality, span membership and inverse squared
norms. `FiniteRowGramInverse.lean` reconstructs each span vector and
identifies the dual Gram as the actual inverse. Its trace is the inverse
squared distance sum. `FiniteRowNegativeSecondMoment.lean` supplies the
spectral conversion and identifies the conjugated-row Gram with `A A*`.
The actual rectangular singular values therefore satisfy the negative
second-moment identity. `GaussianRectangularDistances.lean` applies it:
for `k` shifted Gaussian rows in `n` columns, all singular values are
positive and the inverse moment is at most `8*k/(n-k+1)`, except with
probability at most `k*2^(-(n-k+1))`, uniformly in deterministic shifts.

`GaussianRowRestriction.lean` derives injective coordinate selection from
actual independence and checks the law of every selected square-matrix
row family. `ComplexRowDistanceScaling.lean` proves exact complex scaling
of each distance, including the conjugated matrix rows.
`GaussianIntermediateSingularBounds.lean` combines these laws with row
interlacing and the literal square-root normalization. All retained
positions of the actual normalized shifted matrix have simultaneous
squared singular-value lower bounds with exponential failure.

`GaussianSmallValueQuantiles.lean` deduces that zero-based position
`n-2*q` has singular value at least `q/(4*n)`, except with probability at
most `n*2^(-q)`, when `0<q` and `2*q<n`. For `q=floor(eta*n)`, its ratio
tends to `eta`, and the geometric failure tends to zero. For
`0<eta<1/3`, the quantile is eventually at least `eta/8`.

`OrderedSmallValueTests.lean` bounds every nonnegative test at most one,
vanishing above a controlled quantile, by the exact tail fraction.
`VaryingProbabilityUpperBound.lean` proves that a deterministic probability
limit inherits any bound holding outside a vanishing bad event.
`GaussianWeakLimitSmallValues.lean` applies these results and a continuous
cutoff: every actual shifted Gaussian weak limiting probability measure
has `nu([0,t))<=48*t` for every `t>0`, uniformly in the shift. The general
shifted weak law supplying this input is now constructed below.

`GaussianWeakLimitLogIntegrability.lean` combines the mass and upper support
bounds. Every such law has no atom at zero, an integrable negative logarithm
with integral at most 96, and a finite full logarithmic integral. The
constructed actual law now supplies all inputs at every complex shift,
so these conclusions are unconditional, as proved below. Zero-shift
Catalan enumeration and identification of the logarithmic
integral with the circular potential are proved below.

The first-moment input at general shifts is now proved in
`GaussianShiftedMomentMeanLimits.lean`. Every actual even singular-moment
mean converges at every complex shift to a finite, nonnegative value;
the complex Gram-trace limit is real and its zeroth value is one.
This module proves mean convergence; the two-word developments below
now prove concentration of the random moments and construct the general
shifted weak law.

`FiniteRelationColorings.lean` identifies assignments satisfying endpoint
equalities with functions on the generated equivalence quotient, giving
the exact count `n^classes`. `FiniteLabeledGraph.lean` allows repeated
edges and loops. `PairedClosedWalk.lean` proves that reversed paired edges
give a connected quotient of a single cyclic walk and at most one more
vertex class than pairs.

`MatrixWordWalks.lean`, `GaussianBijectionPairings.lean` and
`GaussianWordPairingCounts.lean` connect this count to actual ordered
Gaussian products and their integrals. Direct and conjugate positions
are distinct finite types matched by every bijection. Each contribution
is exactly the dimension to its quotient vertex count.
`GaussianWordMeanLimits.lean` removes lower exponents in the limit.
`GaussianNormalizedWordMeans.lean` proves the exact square-root scaling
coefficient for balanced words. `GaussianAllWordMeans.lean` proves mean
convergence for every finite normalized complex word, with empty-word
limit one and unbalanced-word limit zero.

`MatrixScalarShiftWords.lean` expands every shifted matrix word into a
finite list of scalar coefficients and ordered direct/adjoint words,
retaining repeated terms. `FiniteListIntegralLimits.lean` passes actual
integrals and limits through these lists. Their application to the Gram
word proves the stated shifted moment-mean limits. The chosen word-limit
count is proved equal to the exact leading matching count for balanced
nonempty words, zero for unbalanced words and one for the empty word.
General shifted concentration is now proved by the following development.
The logarithmic potential identity remains a required proof obligation.


The second-moment input and the actual weak Gaussian law at every complex
shift are now proved, with no weak-limit assumption. The development
uses the finite matching formula for pairs of arbitrary positive-length
words, including individually unbalanced words and empty matching types.

`PairedTwoClosedWalks.lean` proves that a cross matching connects the two
cyclic walks in their endpoint quotient. This bounds the combined vertex
count by the number of direct factors plus one. `GaussianTwoWordPairings.lean`
identifies actual trace-product integrals with the finite combined-pairing
sum. `GaussianWordPairingBalance.lean` removes the existence-of-pairing
premise, using the checked imbalance cancellation on the empty branch.

`SumBlockBijections.lean` restricts every block-preserving bijection to its
two component bijections. `PairedSumColorings.lean` proves exact additivity
of the generated quotient's vertex count via its coloring bijection.
`GaussianSeparateWordPairings.lean` connects these to the actual separate
matchings and proves that their contribution is exactly the product of
single-word means. `GaussianTwoWordCovariance.lean` cancels those terms,
leaving the cross sum. `GaussianNormalizedWordCovariance.lean` proves the
actual square-root scaling coefficient, identifies normalized covariance
with that cross sum, bounds its norm by the total direct count's factorial
divided by dimension, and proves covariance tends to zero for every pair
of finite words. Empty-word covariances vanish identically.

`FiniteListSecondMoments.lean` retains every ordered term pair and its
multiplicity and justifies both finite integral passages by actual product
integrability. `GaussianShiftedSecondMomentLimits.lean` applies the word
covariance limit to the scalar-shift expansion: each actual normalized
shifted trace second mean tends to the square of its first mean limit.
`GaussianShiftedMomentConcentration.lean` uses Hermitian reality and the
checked centered-square integral identity to prove mean-square and
probability convergence of every actual even singular moment at every
complex shift, including zeroth order.

`GaussianShiftedSquaredMoments.lean` squares the actual singular values
to supply all natural moment limits, together with the vanishing failure
event for the radius `(128+norm(z))^2`. `GaussianShiftedWeakLimit.lean`
applies compact moment existence and continuous-test convergence, then
maps through the nonnegative square root. This constructs the unique
actual singular weak limiting probability law at every complex shift,
with exact even moments and support below `128+norm(z)`. At zero it is
proved equal to the previous zero-shift construction.

`GaussianShiftedLimitProperties.lean` supplies this constructed law to
the checked quantile implications. Unconditionally at every shift it has
`nu([0,t))<=48*t`, no zero atom, negative logarithmic integral at most 96
and finite full logarithmic integral. Uniqueness of probability and mean
limits identifies its second moment as `1+norm(z)^2` and fourth moment as
`2+4*norm(z)^2+norm(z)^4`; actual fourth-moment convergence is also proved.

The circular-potential value of this finite logarithmic integral is
identified below. SSS25 Fact 10.2's transfer to the actual sparse Bernoulli
singular array is also proved below. The full logarithmic squeeze inputs
and the imported circular-law results remain open. No named manuscript status is promoted
by these Gaussian supporting proofs.


The leading counts for arbitrary Gaussian words are now identified with
compatible noncrossing pairings, without a tree or noncrossing assumption
on the actual pairing. `FiniteLabeledTrees.lean` proves that the maximal
connected vertex count excludes both loops and repeated unordered edges
and forces a tree with bijective label-to-edge map. `GaussianWordEdgeLabels.lean`
identifies the exact two positions in each label fiber and the actual
unordered quotient endpoints. `GaussianWordLeadingTrees.lean` consequently
extends the leading-tree characterization to every direct/adjoint order.

`TreeEdgeCuts.lean` proves that deleting a tree edge separates its endpoints
and that its side predicate is constant across all other edges.
`FiniteCircularCuts.lean` identifies a finite cyclic predicate with exactly
two switches, including the wrap at the last position, with its explicit
circular interval. `GaussianWordTreeCuts.lean` applies this to the actual
leading quotient graph: the only switches are at the direct position and
its matched adjoint, and every other pair has both positions on one side.
This proves that every leading pairing is noncrossing.

`FiniteLabeledSeparators.lean` proves the converse graph mechanism. Vertex
predicates that separate their own labeled edge and are constant across
the others make every edge a bridge, exclude repeated edges and loops,
and force exactly one more vertex than labels in a connected graph.
`GaussianWordNoncrossingCounts.lean` proves that each noncrossing circular
cut respects all reversed endpoint identifications and descends to the
actual quotient. These descended predicates supply the separator theorem,
so every noncrossing compatible pairing has the maximal vertex exponent.
Thus leading and noncrossing are equivalent at every positive word length.

The same module proves that every normalized complex word mean tends to
its exact compatible noncrossing-pairing count, including zero for
unbalanced words and one for the empty word. Each constructed shifted
limit's even moment, and each actual shifted singular moment probability
limit, is the finite scalar-shift expansion weighted by these counts.
Their alternating Catalan enumeration and logarithmic-potential
identification are proved below; no named manuscript status is promoted.

`GaussianNoncrossingIntervals.lean` proves that every actual noncrossing
pairing preserves the strict interval between either pair's endpoints.
At first position zero it also preserves the final interval after the
first partner. Restricting the actual bijection to these intervals gives
equal direct and adjoint counts. `GaussianWordRestrictions.lean` identifies
the image of any injective position map with the smaller word's positions,
restricts image-preserving matchings, and proves that increasing maps
preserve the noncrossing condition.

`GaussianFirstPairRestrictions.lean` supplies the actual increasing maps
onto the strict interior and final interval, proves their exact ranges,
and constructs both noncrossing smaller-word matchings. Their images agree
with the original matching, their direct and adjoint counts agree, and
both lengths are strictly smaller. The circular-cut and noncrossing
definitions now also allow length zero; their predicates at every positive
length are unchanged. Empty intervals are included in the restriction
theorems. Reconstruction from smaller matchings and the resulting Catalan
count recurrence are now proved below. These supporting results do not
change manuscript-result statuses.

`GaussianFirstPairAssembly.lean` gives explicit equivalences from the
endpoint/interior/final partitions to the actual direct and adjoint
position fibers. Combining the two smaller matchings with the endpoint
pair constructs a full compatible matching, with exact formulas on each
piece. `GaussianFirstPairNoncrossing.lean` checks every pair of pieces:
increasing maps preserve cuts inside a piece, and every other piece lies
outside both endpoints. Assembly therefore preserves noncrossing.

`GaussianFirstPairDecomposition.lean` keeps each first partner fixed and
proves that assembly and restriction are inverse. Partitioning the actual
noncrossing matchings by this partner gives a sigma equivalence and the
exact sum of products of the two smaller noncrossing counts. Empty words
have exactly one matching. `GaussianWordRestrictions.lean` also supplies
the general inverse implication from exact matching images.

`GaussianNoncrossingNegation.lean` exchanges the color fibers and reverses
the actual matching. The four endpoint inequalities prove that noncrossing
is preserved. The resulting injections in both directions give equality
of counts. `GaussianAlternatingWords.lean` parametrizes parity position
fibers, excludes compatible matchings at odd lengths, and proves that the
actual first interior word reverses the alternating colors while the final
word preserves them. `GaussianAlternatingCatalan.lean` reindexes the exact
first-partner count by its odd position, obtains the Catalan convolution,
and proves every even alternating count equals `catalan(k)`, equivalently
`centralBinom(k)/(k+1)`. Every actual normalized Gaussian word mean of even alternating length
consequently tends to this number.

`GaussianZeroCatalanMoments.lean` proves the Gram word is this alternating
word. A general weighted-sum identity shows that the zero-shift scalar
expansion contributes only its full retained word. Every actual zero-shift
even singular moment therefore converges to `catalan(k)` in mean square
and probability, including zeroth order. Both constructed zero-shift
limiting laws have these exact even moments. Uniqueness of probability
limits also identifies the original leading-permutation count at Gram
order `k+1` with `catalan(k+1)`.

The explicit transformed-beta zero-shift law is now identified below.
Its quarter-circle density form and zero-shift logarithmic evaluation are
proved below. The general shifted Gaussian/circular logarithmic identity
is also proved below. The
actual sparse Bernoulli weak-law transfer is proved below. Bernoulli/row-slice
full logarithmic limits still require proofs. No named manuscript status is promoted.

`BetaMeasureMoments.lean` proves that the actual beta measure is supported
in the open unit interval, that its real density is nonnegative and
integrates to one, and that multiplication by a natural power shifts its
first shape parameter. The actual power integral is the ratio of beta
constants, and every such power is integrable for positive parameters.
`BetaCatalanMoments.lean` applies gamma recurrence and the checked Catalan
successor identity. Every natural moment of four times a beta(1/2,3/2)
variable is `catalan(k)`, and its beta constant is exactly `pi/2`.

`GaussianZeroBetaCandidate.lean` places this scaled beta variable in the
compact interval of squared singular values. Its clipping is equal to
four times the beta variable almost everywhere, and all its moments are
the actual Gaussian compact moment limits. `GaussianZeroBetaIdentification.lean`
uses compact polynomial approximation to prove actual Gaussian weak
convergence to the candidate's square-root image. Uniqueness identifies
both existing zero-shift limits with this image, and almost-everywhere
equality removes the clipping: the actual singular limiting law is the
pushforward of beta(1/2,3/2) under `sqrt(4*x)`.

`GaussianZeroBetaProperties.lean` supplies the explicit beta-coordinate
density integral for every strongly measurable test and proves the sharp
support `[0,2]` for both actual zero-shift limits. The checked logarithmic
integrability of the Gaussian law transfers to the beta logarithm. The
actual singular logarithmic integral is `log(2)` plus one-half the beta
logarithmic moment. The next modules evaluate this reduction and identify
the quarter-circle density form. The general shifted circular-potential
identity and Bernoulli weak-law transfer are proved below. Complete
Bernoulli logarithmic limits are proved below; row-slice logarithmic limits remain open. No
named manuscript result is promoted by these zero-shift supporting proofs.

`BetaHalfMellin.lean` uses the continuous kernel `sqrt(1-x)`, which vanishes
for `x>=1` and is bounded near zero. The checked Mellin differentiation
theorem applies at every positive real parameter, and the real transform
equals the actual unnormalized beta integral. `BetaHalfLogMoment.lean`
compares the derivative at `1/2` with the Gamma quotient derivative. The
checked Gamma derivatives at `1/2` and `2` cancel the Euler constant,
giving the actual beta logarithmic moment `-2*log(2)-1`. There is no
derivative or integrability assumption in this value theorem.

`GaussianZeroLogValue.lean` applies the beta logarithmic reduction. Both
actual zero-shift singular limiting laws have logarithmic integral
`-1/2`, equal to `circularLogPotential 0`. The negative logarithmic
integral agrees with the manuscript's `circularPaperPotential 0`.

`BetaQuarterCircleChange.lean` proves that `s^2/4` maps `(0,2)` injectively
onto `(0,1)`, with derivative `s/2`. Its Jacobian transforms the beta
density into `sqrt(4-s^2)/pi`. `GaussianZeroQuarterCircle.lean` normalizes
that density to a real probability measure, then maps the coordinate
into `NNReal`. Equality of indicator integrals identifies this image
with both actual Gaussian zero-shift limiting measures. Actual empirical
weak convergence and the density integral for every strongly measurable
real test are proved. The logarithm is integrable under this law, and
both its measure integral and explicit density integral equal `-1/2`.
Identification at general complex shifts and Bernoulli weak-law transfer
are proved below. Complete Bernoulli logarithmic limits are proved below; row-slice logarithmic limits remain open. These proofs do not
promote any named manuscript result.


`GaussianSmallDistanceTails.lean` proves linear squared-distance tails
under the actual shifted Gaussian row law. `GaussianSmallestPolynomial.lean`
uses row restriction and negative second moments to bound the probability
of any normalized singular value below `n^(-2)` by `exp(1)/n`.
`GaussianUniformQuantiles.lean` takes a simultaneous union over ranks;
its failure bound `n^2*2^(-floor(sqrt(n)))` tends to zero. Outside the bad
set, ranks greater than `2*floor(sqrt(n))` have singular value at least
`rank/(16*n)`.

`BottomRankLogEntropy.lean` derives the factorial entropy lower bound
from the checked Stirling estimate and reverses the finite bottom-rank
sum exactly. `GaussianGoodLogBounds.lean` bounds a bottom sum of size R
by `4*floor(sqrt(n))*log(n)/n + (R/n)*(log(16*n/R)+1)` outside the two
actual bad events. `GaussianBottomLogRates.lean` proves that the first
term vanishes, and for `R=floor(eta*n)` the other tends to
`eta*(log(16/eta)+1)`, which tends to zero as eta tends to zero.

`NegativeLogBottomClipping.lean` bounds the empirical clipping excess
by the actual bottom negative-log sum. `GaussianNegativeLogClipping.lean`
chooses a fixed small fraction and a fixed clipping threshold; for every
positive error tolerance the actual Gaussian clipping-error probability
tends to zero. The zero-singular-value event is included explicitly.

`GaussianLogConvergence.lean` combines these unconditional estimates
with the actual shifted weak law, the finite limiting logarithmic
integral, the checked second-moment bound and full rank. Both logarithmic
parts and the full empirical logarithm converge in probability at every
complex shift to the constructed law's logarithmic integral. The actual
Gaussian spectral logarithmic potential has the same limit. At zero
the value is `-1/2`. General-shift identification with the circular
potential and Bernoulli weak-law transfer are proved below. Bernoulli/row-slice
full logarithmic limits remain open. No named manuscript status is promoted.


`EmpiricalFullLogPrefixConvergence.lean` partitions the actual finite
index set into its retained prefix and bottom values, with the original
normalization n. The negative-log difference equals the bottom sum
exactly. Checked uniform integrability gives vanishing bottom means,
and positive-part control supplies the full untruncated prefix limit
for every deterministic removed fraction tending to zero.

`GaussianLogTailReduction.lean` discharges every hypothesis of the
extended negative-log tail lemma for the actual shifted Gaussian law.
Its extended negative-log tail is uniformly integrable in probability,
and every extended bottom-r sum tends to zero when r=o(n), retaining
infinity at zero. `GaussianLogPrefixConvergence.lean` gives every such
actual Gaussian prefix its full logarithmic limit, including the
manuscript's literal rounded prefix, denominator n and negative sign.
The prefix zero event is null for each positive matrix dimension.

`BernoulliGaussianPrefix.lean` uses the proved Gaussian limiting mass
and support bounds to choose one decreasing positive fraction along
which both actual matrix laws' signed prefixes converge to the same
limiting integral. Bernoulli weak convergence to the constructed
Gaussian law is now supplied under the degree hypotheses by the proof below. No Bernoulli full-log
limit is inferred without the remaining minor and upper estimates.

`GaussianShiftRotation.lean` proves unit-multiplication invariance of
the actual independent Gaussian matrix law, including a measurable
embedding so event-probability transfer does not need an extra event
measurability premise. Rotating both matrix and shift preserves the
Gram matrix exactly. Uniqueness of the actual weak limit identifies
the complete limiting singular measures at every pair of equal-radius
shifts; their full logarithmic integrals are therefore equal. The
general-shift Gaussian/circular identity is now proved by the radial
value calculation below. Bernoulli weak transfer is proved below. Minor
estimates and final regime conclusions remain open; no named manuscript result is promoted.


`HermitizedResolventDerivatives.lean` differentiates the actual Hermitized
resolvent integral with a checked local dominating bound.
`GaussianRegularizedLogDerivative.lean` supplies the actual regularized
logarithmic integral and its derivative. `GaussianRegularizedLogBounds.lean`
fixes its normalization at infinity; `GaussianRegularizedLogValue.lean`
therefore identifies it with the explicit Dyson expression.
`GaussianRegularizedLogRemoval.lean` removes regularization by dominated
convergence. `GaussianHermitizedZeroLimit.lean` proves the resolvent's limit
`sqrt(1-r^2)` inside the unit disk and zero for `r>=1`, including the boundary.
`GaussianShiftedLogValue.lean` computes the actual limiting logarithmic
integral as `(norm(z)^2-1)/2` inside and `log(norm(z))` outside, at every
complex shift. It equals the independently constructed circular potential.
`GaussianCircularLaw.lean` discharges every Gaussian hypothesis of direct
hermitization and proves full bounded-Lipschitz convergence of its actual
ESD to the uniform unit disk. `BernoulliGaussianCircularPrefix.lean` gives
both literal comparator prefixes the actual paper circular-potential value,
under the degree hypotheses, with Bernoulli weak-law transfer now supplied
by the proof below. The named
row-slice main theorem and both regime conclusions remain unproved.

`BernoulliCenteredEntryWords.lean` proves the exact centered marginal moments
`(1-p)*(-p)^k+p*(1-p)^k`, singleton cancellation, variance `p*(1-p)` and
absolute higher-moment bound by `p`. Fubini gives the actual product-law
entry-word integral as the product of these moments at every multiplicity.
For words with no singleton entries its absolute integral is at most
`p^(distinct entries)`, and twice the distinct-entry count is at most the
word length. If every entry appears twice the integral is exactly the
variance raised to the distinct-entry count.

`BernoulliMatrixWordMeans.lean` expands the actual centered matrix-word
trace into closed walks and integrates it exactly. The two-trace formula
uses the concatenation of both entry lists, retaining shared entries.
`BernoulliNormalizedWordMeans.lean` retains the literal parameter `p=d/n`,
normalization `1/sqrt(d)`, denominator `n` and direct/adjoint order. It
also expands actual centered shifted Gram powers into their scalar-shift
word integrals. None of these finite formulas assumes weak convergence.

`BernoulliCenteringInterlacing.lean` proves rank at most one for a constant
entry matrix and identifies its adjoint kernel on the coordinate-sum
kernel. The checked kernel spectral comparison gives both singular-value
interlacings with one-index loss for every sample.
`BernoulliCenteringDistribution.lean` turns them into a count discrepancy
of at most one below every real threshold. It identifies the normalized
count with the mass of the actual empirical singular measure, proving a
uniform `1/n` bound when the Bernoulli mean matrix is removed. This is an
unconditional deterministic comparison at every degree and complex shift.

`BernoulliWalkVertexBounds.lean` labels a graph on the actual visited
vertices by the distinct ordered entries. Successor reachability and the
single cyclic orbit prove connectedness. The visited-vertex count is at
most the distinct-entry count plus one; singleton cancellation thus gives
at most half the word length plus one vertices. Maximal vertex count
forces a tree and excludes loop labels. `FiniteKernelColorings.lean`
identifies the colorings of any exact equality pattern with embeddings of
its quotient. Their count is the ambient falling factorial at the quotient
size, is bounded by the corresponding dimension power, and its ratio to
that power tends to one for every fixed pattern.

The actual Bernoulli word-mean limits, their Gaussian leading-count
identification and concentration are proved below. The compact-target
moment argument and centering comparison also prove SSS25 Fact 10.2 below.
Actual Bernoulli full logarithmic limits, the minor and upper estimates,
smallest-singular-value inputs, and both row-slice regime conclusions also
remain open. These additions do not promote any named manuscript status.

`FiniteKernelPartition.lean` supplies a finite type of equivalence relations
on the word positions. Every coloring belongs to exactly one kernel fiber;
the checked fiber equivalence gives a sum over these exact patterns, with
the falling factorial at each quotient vertex count as coefficient.
`BernoulliWalkPatterns.lean` proves that the centered entry-moment product
is invariant under injective entry relabeling. Its canonical quotient walk
therefore evaluates the actual weight of every coloring with that kernel.
This identifies the actual centered matrix trace integral and its sparse
normalization with a finite pattern sum, independently of dimension.
Canonical quotient vertices satisfy `v<=e+1`, and surviving entries satisfy
`2*e<=word length`. Equality in the latter forces every entry count to be
exactly two and its weight to be `(p*(1-p))^e`.

`SparsePatternPowerLimits.lean` separates the even-word normalization into
the falling-factorial ratio, `n^v/n^(e+1)`, and `d^e/d^m`. Their product is
at most one in positive dimension and degree; when `d->infinity`, it tends
to zero unless `v=e+1` and `e=m`. `BernoulliPatternMeanLimits.lean` applies
these bounds to the actual sparse Bernoulli pattern contributions.
Singleton patterns vanish exactly. Every nonleading even pattern vanishes,
while a leading paired pattern contributes one when also `d/n->0`.
Summing over the fixed finite pattern set proves the actual normalized
even word-mean limit. The clipped parameter only totalizes early invalid
dimensions; the unmodified actual normalized mean is identified with the
pattern sum at every valid dimension, and validity holds eventually under
the stated degree hypotheses.

`BernoulliAllWordMeanLimits.lean` proves that odd surviving patterns have an
extra `1/sqrt(d)` factor and hence tend to zero. Odd leading-pattern counts
are zero. Together with the identity word, every finite actual centered
sparsely normalized direct/adjoint trace mean converges to its finite
leading-pattern count. `BernoulliShiftedMomentMeanLimits.lean` proves these
word traces and means are real, then integrates the exact noncommuting
scalar-shift expansion. Every actual centered shifted Gram-trace mean
converges at every complex shift, and the corresponding even singular-moment
mean converges to the real part of that finite expression. These limiting
moment values are nonnegative and the zeroth value is one.

The Gaussian leading-count identification, two-word concentration and
passage from these centered moments to the actual Bernoulli weak singular
law are proved below. The uncentered mean has a rank-one outlier, so these
centered moment limits do not assert uncentered moment convergence; its
weak-law comparison uses the checked `1/n` empirical distribution bound.
The named Bernoulli hermitization proposition remains partial, and named
manuscript coverage remains 23/29. No mathematical dependency is added as
an axiom, and the full row-slice theorem remains a target without proof.

`BernoulliWordCovarianceWeights.lean` subtracts the actual product of word
weights from the joint weight. Entry-disjoint words cancel exactly, joint
singletons vanish, and the surviving covariance weight has absolute value
at most `2*p^e`. `ClosedTwoWalkGraph.lean` proves that a shared ordered entry
connects the actual visited graph of both closed walks. Consequently its
vertex count is at most its distinct-entry count plus one.
`BernoulliTwoWalkPatterns.lean` transports the joint covariance to the exact
quotient pattern, retaining every shared vertex and ordered entry. It
supplies both `v<=e+1` and `2*e<=total length` for the surviving shared
patterns. `BernoulliTwoWordCovariance.lean` groups the actual joint integral
minus the product of its actual means over these kernels, with the exact
falling-factorial coefficients.

`BernoulliNormalizedWordCovariance.lean` supplies both trace normalizations.
Every surviving shared even pattern is bounded by `2/n`, and odd patterns
have an extra `1/sqrt(d)` factor. All remaining patterns are exactly zero.
The fixed finite pattern sum therefore proves that covariance between any
two actual centered normalized words tends to zero under `d->infinity` and
`d/n->0`. `BernoulliWordConcentration.lean` combines this with the actual
word-mean limits through the exact square-error identity: every such word
converges in mean square and in probability to its checked pattern count.
`BernoulliShiftedMomentConcentration.lean` applies finite real weighted sums
to the exact scalar-shift expansion. Every actual centered shifted even
singular moment converges in probability, at every complex shift and order,
to the real part of its finite pattern-count expression. No independence
between different trace words is assumed. Gaussian identification and
actual Bernoulli weak-law transfer are proved below; named coverage stays 23/29.


`ClosedWalkTreeOrientation.lean` removes one tree edge and uses its cut to
show that every ordered edge of a maximal closed walk appears with both
symbols. `BernoulliLeadingPartners.lean` combines this with the exact
two-occurrence fiber size: every position has one opposite-symbol partner,
and this partner map is an involution. The resulting direct-to-adjoint
bijection is an actual Gaussian word pairing.

`BernoulliLeadingGaussianKernel.lean` maps the matching-generated vertex
quotient onto the original Bernoulli quotient. Their exact cardinalities
force bijectivity, identifying the generated setoid with the original
vertex kernel. `GaussianLeadingBernoulliPatterns.lean` proves the reverse:
a maximal Gaussian pairing has distinct nonloop ordered entries with
exactly two occurrences and gives a leading Bernoulli kernel.
`BernoulliGaussianWordCounts.lean` checks the inverse constructions and
identifies every Bernoulli word count with the Gaussian word count,
including unbalanced and empty words. All actual centered words and shifted
even singular moments therefore converge in probability to the previously
constructed Gaussian limits.

`PolynomialMomentTailApproximation.lean` bounds a polynomial's growth by
its coefficient sum and degree. Outside an approximation interval, a
higher actual empirical moment bounds the error of a bounded continuous
test. The compact target's higher moments are bounded by powers of its
support radius, so selecting a sufficiently high order makes the target
error arbitrarily small. `CompactTargetMomentConvergence.lean` uses these
bounds to deduce bounded-continuous test convergence from convergence of
all actual moments to a compact target, without a compact-support premise
on the finite samples. `BernoulliCenteredWeakLimit.lean` applies this to
the actual squared singular values and pushes the result through the
nonnegative square root, proving the centered weak law at every shift.

`ClippedInterlacingMeanBounds.lean` telescopes the two one-index
interlacings to bound clipped mean distance by `2*S/n`.
`InterlacedContinuousMeanComparison.lean` combines uniform continuity on
the clipping interval with the empirical upper-tail fraction.
`InterlacedEmpiricalWeakTransfer.lean` controls that fraction using a
bounded continuous cutoff and the compact target's support. Every bounded
continuous test transfers through the interlacing.
`BernoulliGaussianWeakTransfer.lean` supplies the actual rank-one mean
comparison and proves the actual uncentered sparse Bernoulli weak singular
law at every complex shift, under `d->infinity` and `d/n->0`. This checks
SSS25 Fact 10.2 and part (i) of the Bernoulli hermitization proposition.
The two common Gaussian/Bernoulli prefix modules now supply this proof and
require only the degree hypotheses. Part (ii), the full Bernoulli
logarithmic limit, remains open; the named proposition stays partial and
named coverage stays 23/29.


`SparseRealPatternPowerLimits.lean` removes the integer-degree restriction
from the sparse power budget. The real effective degree is `m*p`, and a
positive limiting minor/ambient dimension ratio makes it tend to infinity.
`ParameterBernoulliWordMeans.lean` gives the actual arbitrary-probability
centered matrix, trace means and exact pattern sum. Leading contributions
have the variance factor `(1-p)^k`; singleton and nonleading contributions
vanish. `ParameterBernoulliMeanLimits.lean` proves every actual word mean
has the Gaussian count as limit, for any growing dimension sequence with
`p->0` and `m*p->infinity`.

`ParameterBernoulliWordCovariance.lean` retains the exact joint-kernel
formula and checks the same `2/m` dimension loss, with an extra inverse
square root of real effective degree for odd length.
`ParameterBernoulliWordConcentration.lean` combines these covariance limits
with the actual centered-square identity, proving mean-square and
probability convergence of every word. Finite scalar-shift assembly in
`ParameterBernoulliShiftedMoments.lean` gives every actual centered shifted
even singular-moment limit.

The polynomial mean theorem now permits arbitrary finite index types.
The compact-target moment theorem and the one-index interlacing theorem
also permit dimensions independent of the sequence index, while retaining
the original statements as checked special cases.
`ParameterBernoulliWeakLimit.lean` supplies these results and restores the
actual rank-one mean, proving the uncentered weak law under effective-degree
normalization at every fixed complex shift.

`BernoulliPrincipalMinorLaw.lean` proves that restricting the actual
independent ambient entries to any principal minor gives exactly the
product Bernoulli law with unchanged ambient probability. It retains the
source ambient normalization in a checked matrix identity.
`BernoulliPrincipalMinorWeakLimit.lean` checks the positive-ratio effective
and dimension limits and transfers the arbitrary-parameter weak law through
that actual restriction. This includes the literal manuscript minor floor
at every fixed fraction below one. An exact finite identity divides the
source minor by `sqrt(m/n)` and rescales its shift, giving the effective-degree
matrix. The varying rescaling and shift passage is now proved below. The
common minor logarithmic-prefix limit is proved below; the full-to-minor
upper estimate remains open.
The full Bernoulli logarithmic assertion is not inferred from weak
convergence. Named coverage remains 23/29.

`SquareSingularPerturbationBounds.lean` proves ordered singular-value
comparison directly from adjoint norm bounds. Each singular value scales
exactly under scalar multiplication and changes by at most the shift norm
under a scalar identity shift. `RelativeEmpiricalWeakTransfer.lean` uses
a bounded continuous upper-tail cutoff and uniform continuity on a compact
interval to transfer a weak law under vanishing relative pointwise errors.
`ScaledEmpiricalWeakTransfer.lean` therefore transfers every compact-target
weak law through convergent positive scales and vanishing scalar shifts.

`BernoulliPrincipalMinorAmbientWeakLimit.lean` applies this transfer to the
actual restricted ambient sample and retains the source normalization. A
positive limiting minor dimension ratio theta gives the sqrt(theta)
pushforward of the actual Gaussian law at shift z/sqrt(theta).
`GaussianMinorLimitProperties.lean` checks the scaled law's linear mass
bound near zero, compact support and finite logarithmic integral. Its
negative logarithmic value is exactly the circular potential at the
rescaled shift minus log(sqrt(theta)), and tends to the full circular
potential as theta tends to one. This includes shifts on the unit circle.

`IndexedRetainedPrefixSmallValues.lean` permits the sequence index and
array dimension to differ in the weak-law retained-value bound.
`BernoulliPrincipalMinorSmallValues.lean` checks that the literal second
manuscript floor omits at least epsilon/4 of the minor's dimension. For
each fixed fraction in (0,1), its retained singular values have a fixed
strictly positive lower bound with probability tending to one, and its
retained-zero probability vanishes. The common minor logarithmic-prefix
convergence is now proved below; the full-to-minor upper estimate is proved below.
Named coverage remains 23/29.

`BernoulliPrincipalMinorSecondMoment.lean` transports the actual minor
second moment through the restriction law and proves a uniform expectation
and Markov tail bound with the source ambient normalization.
`LinearMassLogClipping.lean` derives exponential-tail integration from the
layer-cake formula and bounds negative-log clipping errors under a linear
small-value mass bound. It derives zero mass and handles the totalized
logarithm at zero almost everywhere. `GaussianMinorUniformLogBounds.lean`
provides uniform clipping and support constants when the minor ratio is
at least one half.

`MinorLogPrefixDeviation.lean` combines retained-value positivity, clipped
weak tests and second moments to bound the literal minor logarithmic prefix.
Its finite identity retains the ambient denominator and both source floors.
`MinorLogarithmicStages.lean` supplies vanishing deterministic tolerances,
the exact dimension-rounding errors and the limiting circular value.
`BernoulliMinorLogStageBounds.lean` gives eventual stage readiness and a
four-event probability bound for the actual ambient Bernoulli law.

`BernoulliCommonMinorLogPrefix.lean` combines these bounds with the full T1
slow-choice theorem. Both actual literal prefixes converge to the circular
potential along the same positive antitone fraction tending to zero, and the
minor retained-zero probability vanishes. Every mathematical premise is
supplied under the degree hypotheses; optional eventual constraints survive
the common choice. This proves the common slow-fraction limits needed for
full-log assembly and does not assert exact fixed-fraction prefix limits.
`BernoulliMinorUpperReduction.lean` uses this common choice to reduce the
actual full Bernoulli logarithmic limit to the fixed-fraction full-to-minor
upper estimate with a vanishing deterministic error. That estimate remains
an explicit premise supplied by the greedy process below. The full
Bernoulli hermitization proposition and its bottom-tail corollary are proved.

The full-to-minor upper estimate corresponds to SSS25 Lemma 8.2 and is proved below. Its
[source proof](https://arxiv.org/html/2310.17600v2) derives the comparison
from completion of an incremental row/column exposure process. Lemma 8.1
uses the step estimate in Lemma 7.1, the high-probability event of Lemma 8.3
and the drift bound of Lemma 8.4. The drift bound and good-event coupling
are now checked below, as is uniform coordinate-spread basis existence.
Actual graph-event probabilities, the small-dimension projection regime
and alternating row/column process assembly remain open;
the full-to-minor upper estimate is not discharged by the minor weak law.

`ExposureProcessDrift.lean` proves the conditional exponential-moment
argument over the actual filtration, permitting downward control only
above the moving barrier. Initial height and bounded upward steps give
integrability. The terminal error bound is independent of the number of
steps. `ExposureProcessCompletion.lean` converts this to the source
`4*q^(1/8)` probability bound, including q=0 and large q.
`HalfIntegerExposureDrift.lean` proves exact measurable reconstruction of
the doubled height and preserves the source barrier and downward-step
event. Its `sss_exposure_drift_lemma` has the source conditional success
probability hypothesis and conclusion of SSS25 Lemma 8.4.

`ExposureGoodEventCoupling.lean` kills the height when a nested currently
measurable good event fails. Conditional indicator comparison and the
pull-out property prove that killing preserves drift without conditioning
on the final good event. Terminal failure is at most the final good-event
failure plus `4*q^(1/8)`. A varying-sample-space limit permits arbitrary
matrix dimensions and numbers of steps. This supplies the probabilistic
assembly in Lemma 8.1, while keeping its actual graph and projection
probability inputs explicit. No named manuscript result is promoted.

`MatrixSingularVolumes.lean` permits arbitrary finite row types, including
the disjoint union that represents a newly inserted row. A coisometric
row compression has an isometric adjoint, so the checked ordered spectral
comparison bounds its Gram determinant by the squared leading singular
product. `LeadingRowSingularCompression.lean` selects the first r sorted
left-singular directions, using the same finite-type equivalence as the
spectral theorem. Their actual Gram determinant equals the squared old
leading product.

`RowKernelProjection.lean` proves that the unregularized inverse-Gram
formula is self-adjoint, idempotent and exactly the orthogonal projection
onto the matrix kernel. A full row Gram also gives surjectivity and the
exact kernel dimension. `InsertedRowSingularVolume.lean` proves the exact
base-times-height Gram determinant identity with this actual projection.
`RowAdditionSingularProducts.lean` combines it with coisometric compression:
for r<=n, the leading r+1 new singular product dominates the old leading
r product times the projection norm. The zero old-product case is proved
separately, so no full-rank assumption is hidden in the product bound.
This checks the kernel-projection row-insertion form used in SSS25 Lemma 7.2.

`LeadingRowKernelGeometry.lean` checks the vanishing sorted coordinates,
dimension m-r when the old product is nonzero, and the near-kernel norm
bound at the next old singular value. At r=n its kernel equals the full
matrix kernel. `RowAdditionSingularInterlacing.lean` proves that deleting
the new row is a coisometry and supplies the large-next-singular-value
branch of the exposure step. `RowAdditionLogIncrement.lean` identifies
the actual retained log sums with negative log products on positive
products. Either branch gives the normalized logarithmic increment.
The logarithmic step-failure probability is at most the projection-small
probability. The actual Bernoulli bound and the coordinate-spread basis
construction are now proved below. The small-dimension projection regime,
graph events and alternating row/column process remain open. The full-to-minor upper estimate is still
an explicit input. Named manuscript coverage remains 23/29.

`RectangularAdjointSingularValues.lean` proves equality of common ordered
singular positions for a rectangular matrix and its adjoint, including rank
deficiency. `ReindexedMatrixSingularValues.lean` proves invariance under
finite row and column permutations. `ColumnAdditionSingularProducts.lean`
and `ColumnAdditionLogIncrement.lean` transfer the actual product and log
steps to column insertion, with the left-kernel dimension and near-kernel
bound. `LastIndexMatrixInsertion.lean` identifies literal last-row and
last-column deletion with those insertion steps. Same-prefix products
increase under insertion, and their negative logarithms decrease when the
old product is positive.

`WeightedBernoulliSymmetrization.lean` computes the exact symmetrized
truncated second moment of the weighted Bernoulli law and identifies its
product-sum law with the actual cube pushforward. For `0<p<=1/2`, at least
k coefficients of modulus at least rho and radius `t>=rho/2`,
`WeightedBernoulliSmallBall.lean` proves the uniform complex scalar bound
`C*(t/rho)/sqrt(k*p)`, with `C=48*exp(1)/pi`. This supplies a checked scalar
anti-concentration input without assuming a projection probability.

`BernoulliProjectionSmallBall.lean` proves the exact orthonormal-coordinate
projection energy identity. Projection energy at most `h*t^2/2` forces at
least half of h coordinates to have modulus at most t. Integrating that
count and using the scalar bound gives actual projection probability at
most `2*C*(t/rho)/sqrt(k*p)` if every basis vector has at least k coordinates
of modulus at least rho. Arbitrary deterministic shifts are included.
`BernoulliExposureSmallBall.lean` applies this to the actual row and column
log-step failure events, including the conjugation of the inserted row.
The compatible-radius hypothesis is explicit. Basis existence is proved
below; the small-dimension graph-spread projection regime and graph-event
probabilities remain open, as does the full-to-minor upper estimate.
No named manuscript result is promoted.

`RademacherLinearMoments.lean` proves actual fair-sign second and fourth
moments and the mean-norm bound `sqrt(energy)/8`. `FlatFourierBasis.lean`
constructs a flat complex Fourier orthonormal basis in every positive
dimension. `SignedFourierMixing.lean` computes the coordinate energies of
its actual random-sign mixtures. Coordinate energies of a subspace basis
lie in `[0,1]` and sum to h, so `FourierBasisMass.lean` obtains a basis with
total coordinate mass at least `h*sqrt(h)/8`.

`ExtremalBasisMass.lean` proves compactness of orthonormal frames and
existence of a basis maximizing total coordinate mass. The normalized
sum/difference rotation in `BasisPairRotation.lean` forces any two of its
vector masses to differ by at most four. `UniformBasisMass.lean` therefore
gives `sqrt(h)/32` for every vector. Cauchy-Schwarz in
`UniformBasisSpread.lean` gives at least `h/4096` coordinates of modulus at
least `sqrt(h)/(64*n)` for every basis vector, including h=1. This supplies
the geometric basis-existence assertion used in SSS25 Lemma 6.3, with
explicit absolute constants and no random-unitary assumption.

`BernoulliSubspaceSmallBall.lean` uses this proved basis for every nonzero
subspace, with `k=ceil(h/4096)` and `rho=sqrt(h)/(64*n)`. Actual Bernoulli
projection and row/column log-step probabilities now have the scalar bound
with no unproved basis-spread input. Positive dimension and compatible
radii are explicit. The small-dimension graph-spread projection regime,
graph-event probabilities and alternating process still need proofs.

`BernoulliProjectionRadius.lean` enlarges the scalar radius by half the
spread radius and controls the ceiling in the coordinate count. The
actual projection bound becomes `C*(kappa+1/sqrt(h*p))`, including ambient
coordinate counts at most n. `BernoulliLargeProjection.lean` proves the
Bernoulli specialization of [SSS25 Lemma 6.2](https://arxiv.org/html/2310.17600v2):
for `d=n*p>=1` and `h>=n*d^(-1/4)`, the actual projection probability at
radius `kappa*sqrt(d)*h^(3/2)*n^(-3/2)` is at most
`C*(kappa+d^(-1/4))`, with `C=16384*(48*exp(1)/pi)`. The exact source
radius conversion and inverse dimension estimate are checked. Arbitrary
deterministic shifts, smaller ambient dimensions and row conjugation are
included. `BernoulliLargeProjectionLemma` is a closed proposition with
the proof `bernoulli_large_projection_lemma`.

`BernoulliLargeExposure.lean` transfers this to the actual row and column
log-step failure events. The comparison of `exp(-N*delta)` with the source
projection radius remains explicit. The small-dimension graph-spread
projection regime, graph-event estimates and complete alternating process
are still open; no named manuscript result is promoted.

`UniqueNeighbourhoodGeometry.lean` checks the restricted-vector observation
behind [SSS25 Section 5](https://arxiv.org/html/2310.17600v2), for rectangular
matrices with an injective embedding of the diagonal. Rows with a unique
selected nonzero entry and rows supplied by the diagonal shift both give
the lower bound `beta*a` when the selected coordinates have norm at least a.

`ShiftedGraphBudgets.lean` counts the actual rows touched by middle
coordinates. This includes nonzero entries of A and the embedded diagonal,
with total count at most the sum of column support sizes plus the middle
set size. An untouched row has zero shifted middle image. The actual
shifted row l1 mass is at most the original row l1 mass plus the shift norm,
which bounds the tail image without assuming an operator-norm estimate.

`UniqueNeighbourhoodAmplification.lean` supplies the actual vector
decomposition and the image-spread conclusion. If the unique-neighbourhood
count is at least b and each of the heavy-row and shifted middle-support
budgets is at most b/4, at least b/2 image coordinates have norm at least
`beta*a/2`. The scalar tail condition is explicit in its general interface.

`GraphCoordinateGap.lean` discharges that scalar condition for the source
row threshold `(d*n/(beta*ell))^5/beta` and gap
`(beta*ell/(d*n))^7`, for `0<beta<=1`, `d>=4` and `0<ell<=n`.
Actual sorted prefixes give the exact middle size `g-1`, including ties,
and a tail bounded by the one-based order statistic at `ell+g`.
`GraphNearKernelGap.lean` derives the squared-image norm lower bound
`b*beta^2*(v*_ell)^2/8` and excludes this coordinate gap when the image
energy is smaller. The graph counts remain hypotheses about actual
supports. The source growth function, iteration and conditional projection
bound are now proved below. Random graph probabilities and instantiation
of the source thresholds remain open. Named coverage remains 23/29.

`GraphGrowthBudget.lean` defines the literal source expansion
`d*x/log(n/x)^2` and ceiling growth
`g(x)=ceil(expansion/(C*(d+log(n/x))))`. With uniform column-degree
constant K, `C=graphGrowthConstant(K+1)=4096*(K+2)^2` is sufficient.
The actual middle set has size `g-1`, and its shifted support count,
including the embedded diagonal, is now obtained from that column-degree
condition. The logarithmic support-size estimate and the fixed constant
comparison are both proved. `SourceGraphGap.lean` therefore derives the
image-spread and near-kernel no-gap statements from uniform actual graph
events. The heavy-row event is required only in the relevant range
`ell>0` and `log(n/ell)>=1`.

`GraphGrowthIteration.lean` checks the actual integer recurrence and its
first exit time: at most `(4*C+2)*log(n/k)^4` steps when the terminal
scale u satisfies `log(n/u)>=1`. The proof obtains a uniform relative
increment and sums the corresponding logarithmic increments; it retains
the integer ceiling. `SourceGraphGrowthRange.lean` checks the exact
terminal scale `u=n*log(log d)/(2*d)` for `d>=exp(exp(1))`, including
`0<u<=n/4` and valid next ranks when the ambient dimension is at least
n/2. This supplies the numerical assertion used in SSS25 Fact 5.4.

`GraphNearKernelIteration.lean` also gives the terminal-scale source
coordinate-gap statement with automatic logarithmic and rank conditions.
For the whole recurrence it propagates an actual initial modulus a and
proves coordinate spread beyond u at the explicit radius
`R=a*((beta*k/(d*n))^7)^T`, with
`T=ceil(4*C*log(n/k)^4)+1`. Its image-energy threshold is
`expansion(n,d,k)*beta^2*R^2/8`. Uniform graph events, the initial modulus
and a strict upper bound below that threshold are the remaining inputs;
the recurrence, first exit, finite ranks and coordinate propagation are
all checked.

`GraphSubspaceSmallBall.lean` applies this to the proved initial spread
basis of a nonzero subspace, with `k=ceil(h/4096)` and
`a=sqrt(h)/(64*m)`. Its graph-amplified basis and actual Bernoulli
projection probability are proved, without an assumed amplified basis.
The general probability bound is `2*C_scalar/sqrt(ceil(u)*p)`.
The assembled terminal-scale bound is
`4*C_scalar/sqrt(log(log d))` when `d=n*p`. Arbitrary deterministic
projection centers are included. The uniform near-kernel energy and
projection-radius comparisons remain explicit and have not been
instantiated with the source `eta_r`. Random graph-event probabilities,
that threshold instantiation and full alternating process assembly remain
open. No named manuscript result is promoted.


`GraphSubspaceSmallBall.lean` now also covers the branch where the initial
basis already has more than the terminal number of spread coordinates.
The graph radius is at most the initial radius when the ambient coordinate
count is at most n, so the same original basis suffices in that branch.
The former seed-count-at-most-terminal restriction is removed.

`GraphLeadingKernel.lean` defines the actual next singular scale, with zero
at full row retention. The checked singular geometry proves the uniform
squared-image estimate on every vector in the actual leading-row kernel.
Its dimension is exactly m-r on a nonzero old singular product, and its
seed coordinate count is exactly `ceil((m-r)/4096)`. This supplies the
terminal graph projection probability with no assumed basis and no assumed
uniform near-kernel estimate.

`BernoulliGraphExposure.lean` checks that a failed row or adjoint-column
logarithmic step forces this actual scale below `exp(-N*delta)`. In the
other branch interlacing makes failure impossible. The actual Bernoulli
failure probability is therefore at most
`4*C_scalar/sqrt(log(log d))` under the uniform graph events and the two
explicit comparisons of the squared threshold with the graph energy and
projection radius. The full-row kernel case is included. Random graph
event probabilities, source `eta_r` comparisons and alternating process
assembly remain unproved. Named manuscript coverage remains 23/29.


`GraphProjectionThreshold.lean` supplies a sufficient scalar radius
`beta*sqrt(h)*R/(128*(1+log(N/k)))` for both the strict graph image-energy
comparison and the projection-energy comparison. Its exact exponential
cost cancels the two dimension square roots. `GraphProjectionCost.lean`
bounds that cost by
`64*(C_growth+1)*(1+log(d)-log(beta)+log(N/k))^5`.

`SourceGraphProjectionThreshold.lean` checks the integer exposure guard:
for ambient N, local coordinate count m and retained rank r,
`(N-m)/8<m-r` implies `N-r<=9*(m-r)`, with natural-number division.
The small-rank condition `g=N-r<=N*d^(-1/4)` and `d>=exp(4)` give
`log(N/g)>=1` and `log(d)<=4*log(N/g)`. Thus the exact scalar cost is at
most `C_source*log(d)^8*log(N/g)^8`, where
`C_source=64*(C_growth+1)*(22-log(beta))^5` and
`C_growth=graphGrowthConstant(K+1)`.

`BernoulliSourceGraphExposure.lean` discharges the raw graph threshold
comparisons in the actual row and adjoint-column log-failure bounds.
`SourceLargeProjection.lean` completes a square for the raw squared-log
threshold and proves an inverse dimension bound when global remaining
size is at most nine local dimensions. `BernoulliSourceExposure.lean`
combines both raw-matrix log-step branches into an error tending to zero
with the degree. These raw-matrix results alone do not give the normalized
insertion process used by the paper.

`NormalizedGraphThreshold.lean` retains the normalized projection factor
`sqrt(d)`. The source exponent dominates `log(d)`, so doubling its explicit
coefficient makes `sqrt(d)*exp(-2*E)<=exp(-E)` and supplies both scalar
comparisons on the actual leading-row kernel. `NormalizedLargeProjection.lean`
checks the other normalized projection branch. For `log(N/g)>=4` and
`g/N<=epsilon`, the actual threshold `sqrt(d)*exp(-log(N/g)^2)` is at most
the proved large projection radius with coefficient epsilon. Its actual
probability is at most `C_large*(epsilon+3*d^(-1/4))`.

`NormalizedSourceProjection.lean` combines these normalized projection
branches on the actual leading-row kernel. A nonzero old product gives
its exact dimension, and the actual next singular scale is assumed below
`sqrt(d)*eta`. Uniform graph events and the integer guard are explicit.
For `epsilon<=exp(-4)`, the probability is at most
`C_large*(epsilon+3*d^(-1/4))+4*C_scalar/sqrt(log(log d))`.
The limit of this bound is checked when epsilon tends to zero and degree
tends to infinity. These are guarded Bernoulli dependencies with explicit
constants and a retained-rank convention. No unrestricted SSS25 Lemma 6.1
or named manuscript result is promoted. The actual normalized insertion
transfer is checked below; random graph-event probabilities, accumulated
log-error bounds and full adapted alternating process assembly remain open.

`RectangularSingularScaling.lean` proves singular-value homogeneity for
arbitrary finite row and column types, including the inserted disjoint-union
row type and zero scalars. Positive degree normalization divides each
actual singular value by `sqrt(d)`.

`InsertionDegreeNormalization.lean` checks that scaling the old matrix
and inserted vector scales the actual inserted row or column matrix.
The retained singular products scale by the appropriate scalar-norm
power, including zero products. On nonzero retained products, the actual
log prefix gains its retained rank times `log(sqrt(d))`.

`NormalizedInsertionLogIncrement.lean` uses these identities to prove
the actual degree-normalized insertion step from raw product growth by
`sqrt(d)*exp(-N*delta)`. Both projection and next-singular-value branches
prove a positive new retained product as well as the log inequality.
Failure is defined to include a zero new product or an excessive actual
normalized log prefix. Its containment in the raw projection-small event
is checked for arbitrary finite measures, in both insertion directions.

`NormalizedSourceExposure.lean` proves that this failure forces the raw
next singular scale below `sqrt(d)*exp(-N*delta)`, with zero scale at
full row retention. Thus the actual normalized row and adjoint-column
Bernoulli failure probabilities obey the combined source error bound
without an assumed next-singular-scale condition. The integer guard,
remaining fraction, positive old product and deterministic graph budgets
remain explicit. The accumulated finite rank-error bound is checked below.
Random graph-event probabilities, the complete adapted alternating process
and full-to-minor upper comparison are proved below. Named coverage stays 23/29.

`NormalizedLogPowerSums.lean` proves, for positive k, positive N and L<=N,
the actual finite bound
`sum_{g=1}^L log(N/g)^k/N <= 2*(2*k)^k*sqrt(L/N)`.
The logarithm is bounded by a small power; the inverse-square-root sum
telescopes. Arbitrary subsets of these ranks are included.

`TwoBranchLogSums.lean` retains the literal small-branch cutoff
`floor(N*theta)`. A schedule with eighth-power coefficient B there and
the squared-logarithm branch elsewhere has actual sum at most
`32*sqrt(L/N)+2*B*16^8*sqrt(theta)`.

`SourceNormalizedLogError.lean` identifies the checked normalized source
schedule with these branches, with theta=d^(-1/4) and
`B=2*C_source*log(d)^8`. Its finite bound is
`32*sqrt(L/N)+4*C_source*16^8*log(d)^8*d^(-1/8)`.
The actual rank interval from N-L through N-1 is reindexed exactly,
retaining natural subtraction. The degree term tends to zero, so the
literal accumulated rank-error sum vanishes when L/N tends to zero and
degree tends to infinity. This supplies a vanishing bound; no sharper
linear-in-fraction bound is claimed.

`LastIndexDegreeNormalizedSteps.lean` transfers the checked normalized
insertion steps to the literal last-row and last-column matrix views.
Both next-singular-value and projection branches preserve positive new
retained products. Keeping the same retained rank also preserves
positivity and cannot increase the actual normalized log prefix.

`BernoulliMinorUpperProbabilityReduction.lean` permits a fraction-dependent
upper failure probability instead of requiring probability zero in the
limit at every fixed fraction. Deterministic error e and probability bound
b both tend to zero as the fraction shrinks. The already checked common
slow-choice construction preserves both actual prefix limits while making
both errors vanish, and proves the full Bernoulli logarithmic limit from
that explicit upper-estimate input. Random graph-event probabilities,
adapted process assembly and the actual full-to-minor upper estimate
remain unproved. No named manuscript result is promoted.

`BernoulliSubsetCountLaplace.lean` proves the exact exponential moment
`(1-p+p*exp(t))^|S|` for the Boolean count on any entry subset under the
actual product law. Its exponential upper bound and Markov tail are checked,
including endpoint parameters. `BernoulliColumnSubsetCounts.lean` identifies
this count with the actual rectangular matrix's column support sum.

`ColumnDegreeEntropyBounds.lean` absorbs the number of column subsets into
the tail exponent. For a set of cardinality ell and `d=N*p>=1`, the degree
threshold `8*ell*(d+log(N/ell))` leaves the exponent
`-3*log(N)-2*d*ell`. The remaining geometric sum is at most one.
`BernoulliColumnDegreeBudget.lean` therefore proves failure probability at
most `N^(-3)` for the actual uniform column-degree budget, for rectangular
row/column cardinalities at most N and for the square/sparse laws.

`HeavyRowsFromColumnDegree.lean` bounds total row mass by `K*N*d` for
unit-bounded entries. If `d>=1`, `4*K<=d` and `0<beta<=1`, the literal source
threshold `(d*N/(beta*ell))^5/beta` gives the actual heavy-row budget at every
positive ell with `log(N/ell)>=1`. `ColumnDegreeRestriction.lean` proves that
injective row/column restrictions preserve the column budget; the heavy-row
budget follows under the same ambient size and effective degree.

`BernoulliGraphDegreeProbability.lean` supplies both graph degree budgets
simultaneously outside a single event of probability at most `N^(-3)` when
`d>=32`, including `d>=exp(4)`. Every injective row/column restriction of the
actual square or sparse Bernoulli matrix obeys them on this same event,
without an additional union-bound loss. Unique-neighbourhood expansion
probabilities, the complete adapted alternating process and the actual
full-to-minor upper estimate are proved below. Named coverage remains 23/29.

`BernoulliAdjointLaw.lean` checks the measure-preserving entry-index swap
and exact adjoint matrix identity. Arbitrary matrix events have the same
probability in both orientations, including the sparse law.
`BernoulliBidirectionalGraphDegree.lean` gives both graph degree budgets
for every restriction of both orientations outside one event of probability
at most `2*N^(-3)` for effective degree at least 32.

`BernoulliRowPatterns.lean` gives exact selected zero and single-one row
probabilities. `BernoulliRowProductLaw.lean` groups the actual entry measure
into its row product law and checks marginals and product integrals.
`BernoulliUniqueRowLaw.lean` identifies graph-row membership and gives
probability `(1-p)^|S|` inside the embedded diagonal set and
`|S|*p*(1-p)^(|S|-1)` outside it, for `0<beta<=1`.

`BernoulliUniqueCountLaplace.lean` proves the actual mean, exponential
moment and lower tail. A threshold at most half the actual mean has
failure probability at most `exp(-mean/8)`. `BernoulliUniqueCountStructure.lean`
retains both exact factors and the actual number of diagonal rows,
which is at most the selected set's cardinality.

`BernoulliUniqueSmallSetFactors.lean` keeps the small diagonal factor
`|S|*p+exp(-t)` when `|S|*p<=1/2`, while the outside factor is at most
`exp(-|S|*p/4)` if `exp(-t)<=1/2`. `BernoulliSquareSmallSetExpansion.lean`
chooses `t=log(N/|S|)` and absorbs the subset count. The cardinality-ell
expansion failure probability is at most
`exp(ell*(1+log(d+1)+d/log(N/ell)-d/8))`, with its numerical range checked.
For `d>=65536` and `log(N/ell)>=64`, this is at most `exp(-d*ell/16)`.

`BernoulliSquareSmallExpansionProbability.lean` supplies those numerical
conditions from `d>=exp(64)` and `ell*p<=1/2`. Summing all cardinalities
proves actual square unique expansion for every set with `|S|>=k>0` and
`|S|*p<=1/2`, outside an event of probability at most `2*exp(-d*k/16)`.
The rectangular exposure case and larger set range are supplied by the
modules below. Adapted assembly and the upper estimate remain open.

### Actual full source unique expansion in exposure matrices

`BernoulliAmbientSmallSetExpansion.lean` retains the original degree
`d=N*p` when the exposed matrix has at least `3*N/4` rows.
`BernoulliRectangularColumnSets.lean` decomposes a set according to
membership of the unmatched final column. Its diagonal row count is
exactly the selected row-subset size. `BernoulliSmallSetFamilyExpansion.lean`
absorbs subset entropy for both families, including the empty row subset.
`BernoulliExposureSmallSetCardinality.lean`, `FiniteSmallSetExpansionUnion.lean`
and `BernoulliExposureSmallExpansionProbability.lean` give uniform
small-set failure bounds `2*exp(-d*k/16)` for a square minor and
`4*exp(-d*k/16)` for a one-column rectangular matrix when `d>=exp(64)`.

`BernoulliLargeSetMean.lean` proves `log(1-p)>=-2*p` for `p<=1/2` and
the actual mean lower bound `N/(4*log(d))` in the larger set range.
`SourceLargeSetExpansionBounds.lean` checks the scalar comparisons at
`d>=exp(1024)`: the source threshold is at most `N/(8*log(d))`, and the
subset entropy is at most `N/(64*log(d))`.
`BernoulliSourceLargeSetExpansion.lean` gives fixed-set failure at most
`exp(-N/(32*log(d)))` and fixed-cardinality failure at most
`exp(-N/(64*log(d)))`. `BernoulliSourceLargeExpansionProbability.lean`
sums this over all cardinalities, for at most N columns.

`BernoulliSourceUniqueExpansionProbability.lean` proves the actual full
`MatrixUniqueExpansionBudget` with terminal scale
`N*log(log(d))/(2*d)`. Its failure is bounded by the small-set estimate
plus `N*exp(-N/(64*log(d)))`, with `k>0` and `0<beta<=1`.
`BernoulliRectangularRestrictionLaw.lean` gives the exact law, matrix
identity and arbitrary event probability for injective row and column
restrictions. `BernoulliRestrictedUniqueExpansion.lean` transfers the
full budget bound to each specified restriction of the actual ambient
matrix or its adjoint. This does not inherit expansion by deleting rows.

Simultaneous schedule bounds and conditional insertion laws are supplied
below. Progressive good events, the actual adapted alternating process
and the full-to-minor upper estimate are proved below.
No named manuscript result is promoted; the source hashes are unchanged.


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
The expected count of close rows gives the probability bound without any
independence of those distance events.
`SmallestSingularDistanceReduction.lean` identifies the combination of
conjugated rows with the literal matrix adjoint action, constructs an
actual unit witness for every ordered singular value, and bounds the
smallest-value failure by the source almost-constant failure probability
plus the average row-distance probabilities. It applies directly to the
uniform shifted row-slice model. These three modules add 17 theorems and
five definitions. LLY26a Corollary 6.8, its leave-one-out variant and the
non-almost-constant small-ball input to Lemma 7.2 still need checked proofs;
no component probability estimate is assumed as a project axiom or claimed
proved. Named coverage stays 23/29 and manuscript sources are unchanged.


`LeaveOneOutUnitNormal.lean` constructs a unit normal for the actual n-1
other rows, including rank-deficient spans. The least-coordinate projection
normal depends only on those other rows. `ShiftedSliceUnitNormal.lean`
checks resampling invariance, its exact shifted scalar row form and the
inclusion of its bad event in an actual almost-constant kernel failure for
the n-1 remaining rows. `LeaveOneOutDistanceProbability.lean` carries out
the independent-row conditioning in
[LLY26a Lemma 7.2](https://arxiv.org/html/2604.10446v1#S7). It combines the
proved distance reduction with the source scalar and almost-constant
component estimates; those probability estimates are explicit premises.
`NonAlmostBernoulliSmallBall.lean` supplies the Bernoulli scalar estimate
outright using the source non-almost-constant coordinate-count condition
and the already proved weighted Bernoulli scalar bound. For the actual
parameter p=d/n, with 1<=d<=n/2, its probability at radius rho/sqrt(n) is
at most C/sqrt(delta*d), uniformly in the center. These four modules add
26 theorems and three definitions. The fixed-degree slice estimate in
[SSS23 Lemma 8.5](https://arxiv.org/html/2310.17635#S8) is proved below. The
square and leave-one-out almost-constant probability estimates remain unproved.
Named coverage stays 23/29 and manuscript source hashes are unchanged.

`UniformEmbeddingRestriction.lean` proves the exact constant-fibre
restriction law for uniform injective sampling. `PairedSliceSampling.lean`
uses that law and a domain permutation to prove the paired representation
of the actual uniform fixed-degree slice, including its conditional law
and scalar form. `FairBooleanSmallBall.lean` proves equality of the actual
half-parameter Bernoulli cube and uniform Boolean counting, then transfers
the checked scalar small-ball estimate. `PairedSliceSmallBall.lean` gives
the resulting bound `C*(r/rho)/sqrt(k/2)` plus the actual uniform-injection
probability that fewer than k pairs have coordinate differences at least
rho. Here 2*d<=n, k>0, rho>0 and r>=rho/2; the pair-count failure probability
is retained as an actual event, not as an assumed probabilistic estimate.
These four modules add 17 theorems and seven definitions toward SSS23
Lemma 8.5. Its full pair-count probability bound is now proved below. The
square and leave-one-out almost-constant probability estimates remain unproved.
Named coverage stays 23/29 and manuscript source hashes are unchanged.

The full SSS23 Lemma 8.5 is now proved in `RowSliceScalarSmallBall.lean`,
with absolute constant `64+2*C_B` and no assumed concentration estimate.
`UniformEmbeddingMarginal.lean` supplies every injective sampling marginal,
and `SeparatedPairMean.lean` proves the actual pair-count mean at least
`delta*d`. `FiniteFiberMean.lean` and `FiniteFiberTower.lean` construct the
literal conditional fibre means and check their tower identity.
`InjectionPrefixCoupling.lean` gives exact bijections between fine-prefix
fibres. `InjectionExposureMean.lean` bounds the genuine exposure-mean
increments from the codomain-swap hypothesis. `FiniteFiberHoeffding.lean`
proves their conditional exponential bound, and
`UniformInjectionConcentration.lean` proves the actual uniform-injection
lower tail. `PairedCountSwap.lean` bounds the separated-count change by two.
`SeparatedPairLowerTail.lean` consequently gives
`P(pair_count < delta*d/2) <= exp(-delta^2*d/64)`.

For `0<d`, `2*d<=n`, positive delta and rho, and every radius-rho level set
of size at most `(1-delta)*n`, actual slice concentration is bounded by
`2*C_B/sqrt(delta*d)+exp(-delta^2*d/64)`. This discharges all inputs of the
closed source theorem. `RowSliceNonAlmostMinimumBound.lean` supplies the
fixed-delta rate `C(delta)/sqrt(d)` and inserts the proved bound into the
actual leave-one-out distance and smallest-singular-value reductions.
Their remaining component premises are the square and leave-one-out
almost-constant probability bounds. These 12 modules add 54 theorems and
13 definitions. No named result is promoted: the imported minimum estimates
and unconditional circular-law regimes remain unproved. Named coverage
stays 23/29, with manuscript source hashes unchanged.

The lower column-degree input in
[LLY26a Section 6](https://arxiv.org/html/2604.10446v1#S6) is now checked
for the actual square and one-row-deleted laws.
`RowSliceEdgeLowerTail.lean` proves the full multiplicative lower Chernoff
bound `exp(-mu*theta^2/2)` from the negative-tilt exponential moment,
without coordinate independence inside a row.
`RowSliceColumnLowerBounds.lean` gives five-sixths column-degree failure
at most `n*exp(-d/72)` in the square law and `n*exp(-d/320)` in the
one-row-deleted law for `n>=11`, retaining the original parameter d/n.
Both bounds imply `n^(-A)` under the explicit conditions
`72*(A+1)*log(n)<=d` and `320*(A+1)*log(n)<=d`, respectively.

`RowSliceColumnSubsetLoads.lean` supplies the full deterministic LLY26a
Lemma 5.2 by the exact total-load identity: any nonempty subset J of
fixed-degree rows has at most `n/r` columns of load at least
`r*d*|J|/n`. Its closed theorem applies to all rectangular samples and
all positive r. `FiniteUniformEmbeddingRestriction.lean` checks every
injective finite-product restriction. `RowSliceRetainedColumnLowerBounds.lean`
then supplies the literal square-sample deleted-row probability bounds
for every injective selection of n-1 rows, with no assumed marginal law.
These five modules add 21 theorems and four definitions. The required
steep-vector exclusion and complete almost-constant probability bounds
are still unproved. No named result is promoted; coverage remains 23/29
and manuscript source hashes are unchanged.

The gradual almost-constant square-adjoint branch of LLY26a Section 6 is
now proved under explicit budgets. `LLYSteepGeometry.lean` defines the
actual three gap classes and proves the coarser norm constant
`B=4*sqrt(n)*(if k1=1 then 1 else (6*d)^(r+1))*d^(3/4)`.
`LLYAlmostConstantBlocks.lean` checks the four bad-coordinate blocks and
the center bounds, using `delta*n<=k3` to preserve the strict finite count.
`LLYColumnSurvivors.lean` counts the actual exceptional columns from
exact total row-subset loads. At least n/2 columns survive; the second
block retains its separate cutoff `9*k2*d/n`.

`SupportAlmostConstantAction.lean` supplies a variable-support triangle
bound. `LLYColumnBadMass.lean` controls actual column-support bad mass,
and `LLYColumnAction.lean` proves the shifted adjoint coordinate identity
and its lower modulus from the five-sixths column-degree condition.
`LLYGradualAdjoint.lean` proves image norm at least `2*d*sqrt(n)/(25*B)`
for every actual unit gradual almost-constant vector. Its failure
probability below that threshold is at most `n*exp(-d/72)`, outright.
The hypotheses retain positive valid ranks, `k2<=k3`, `2*k3<=n`,
`k1<=ell^(r+1)`, `d*k1<=n/9`, `k2*d^(3/4)<=n/1000`, `k3<=n/1000`,
`rho<=sqrt(n)/(5*B)`, `delta*n<=k3` and `norm(zeta)<=4*d/25`.
`LLYAlmostAdjointReduction.lean` bounds the full actual almost-constant
adjoint event by the actual steep event plus this exponential term.
No sharper imported norm constant is used. The steep probability and
complete leave-one-out kernel estimate remain unproved. These eight
modules add 39 theorems and 14 definitions; named coverage remains 23/29,
and no manuscript source is changed.

The gradual retained-right-action branch is now checked by
`LLYRowLoadProbability.lean`, `LLYRowSurvivors.lean`, `LLYRowAction.lean`
and `LLYGradualRetained.lean`. The load events range over every small
coordinate subset before any vector is chosen, and use distinct cutoffs
`16*k2*d/n` and `16*k3*d/n`. At least n/3 rows survive in any retained set
of size at least `99*n/100`. Every actual unit gradual almost-constant
retained image has norm at least `2*d*sqrt(n)/(25*B)` and is excluded from
the retained kernel. The rank-one and other dense cases are included.

`LLYLeaveOneOutReduction.lean` preserves the original square sample and
ambient shifted diagonal. For n>=100 it bounds the actual almost-constant
kernel probability by the actual steep-kernel probability plus
`exp(-(rowLoadRate/4)*n)`. The finite bound retains explicit rank, radius,
shift, density, entropy and dimension budgets. Degree entropy and the
required dimension inequality are discharged eventually, uniformly over
all d>=C*log(n), C>0, with no upper polylogarithmic restriction.
`LLYGradualRadiusBudgets.lean` proves the minimum threshold comparison
from the radius bound, and derives the column top-block budget from
`k1<=floor(n/(16*d))`.

`LLYSmallestReduction.lean` combines the proved scalar estimate and both
gradual branches. Under the explicit budgets, the only remaining
probability inputs are kappa for the actual steep-adjoint event and eta
uniformly for the actual steep leave-one-out kernel event. Its actual
minimum-value failure bound is
`kappa+n*exp(-d/72)+(C(delta)/sqrt(d)+eta+exp(-(rowLoadRate/4)*n))/delta`.
These seven modules add 24 theorems and three definitions. The steep
probabilities, actual source rank choices and exponent bounds remain
unproved; no unconditional named result is promoted. Coverage remains
23/29 and all manuscript source hashes are preserved.

The first LLY steep right-kernel class is now proved by
`LLYFirstSteepGeometry.lean`, `LLYFirstSteepAction.lean`,
`LLYFirstWitnessProbability.lean`, `LLYFirstSteepProbability.lean`,
`LLYFirstWitnessBudgets.lean` and `LLYMinimumFirstSteepReduction.lean`.
The least actual six-degree jump gives the proved norm constant
`B1=sqrt(n)*(6*d)^r`. Every unit first-steep vector has retained image
norm at least `sqrt(d)/(4*B1)` on the simultaneous unique-witness event,
for every spectral shift of modulus at most d. All actual eligible
witnesses contribute to the Euclidean energy; no fixed-vector estimate
is substituted for the uniform event.

Actual witness failure is at most
`(r+1)*exp(-(uniqueWitnessRate/2)*d)`, including the original square
sample with any one row omitted. The exact floor rank supplies
`16*d*k1<=n`; the adjacent clipped-rank ratio supplies the set-pair
entropy bound. Square-root strides satisfy the entropy budget eventually
when `d>=16/(uniqueWitnessRate^2)*log(n)`. The source power-rank ordering
supplies `r+1<=n`, and an explicit logarithmic degree bound gives the
polynomial failure conversion. The dense k1=1 first class is empty and
its actual one-row-deleted kernel probability is zero.

The assembled actual minimum-value bound now retains only the second
and third steep right-kernel probability and the full steep-adjoint
probability as probability inputs. These six modules add 27 theorems
and five definitions. The remaining steep estimates and full source
parameter/exponent assembly are still unproved. No named result is
promoted; coverage remains 23/29 and manuscript source hashes are unchanged.

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

The actual LLY third almost-constant adjoint branch now has its finite
approximation and probability bound. `CenteredSliceAdjointError.lean`
identifies the centered adjoint action with the proved real-to-complex
operator. Zero coordinate sum removes the mean matrix, so a mean-corrected
coordinate error delta costs `(B+norm(zeta))*2*sqrt(n)*delta`; only its
scalar residual epsilon costs `(B+d+norm(zeta))*sqrt(n)*epsilon`.
`MeanCorrectedScalarNet.lean` constructs the finer scalar grid from the
actual error mean, including arbitrary sparse truncation errors.

`LLYThirdSteepNet.lean` retains the manuscript's factor-four gap and the
actual first/second/third LLY ranks. The normalized third class has proved
high, middle and tail coordinate bounds. Its almost-constant center has
modulus at most `1/3`; subtraction and sparse canonical truncation give a
net with ordered gap above `2/3`, zero third-rank tail, and an explicit
three-range cardinality bound. This is coverage of the actual LLY third
class, not an identification with the different rectangular LLTTY classes.

`LLYThirdSteepAdjointProbability.lean` proves the net union bound and the
actual normalized third almost-constant adjoint probability bound. Its
only hypotheses are deterministic rank, degree and approximation budgets.
`LLYThirdSteepNormalization.lean` proves the actual class homogeneity and
norm bound `sqrt(n)*(6*d)^(r+1)*d^(3/4)`, then normalizes every unit-vector
failure, including its actual almost-constant radius and adjoint residual.
The bound is `n^(-A)` plus both literal net cardinalities times
`(4*exp(1)^2*sqrt(d))^k2 *
(4*exp(1)*bernoulliScalarSmallBallConstant/sqrt(k2*d/n))^n`.

`LLYAlmostSteepSplit.lean` preserves almost-constancy in the actual full
adjoint case split. `LLYAlmostAdjointThirdNet.lean` applies the checked first
and gradual estimates together with the third net bound. The full
almost-constant adjoint event now leaves only the second-class probability
as an unestimated event term. The following source budgets discharge
third-net entropy absorption. Second-class bounds, later right-kernel
estimates, and complete source parameter/exponent assembly are still
required. These seven modules add 32 theorems and ten definitions. No
named result is promoted; coverage remains 23/29 and all manuscript
source hashes are preserved.

The actual third-class source parameter budgets are now checked in ten
further modules. `LLYThirdGridBudgets.lean` bounds the polynomial mesh and
each actual grid cost. `LLYThirdNetEntropy.lean` counts all support choices
and the fine scalar grid without replacing the finite nets by an assumed
cardinality. `LLYSourceRanks.lean` uses the literal rounded LLY26a Section 6
rank choices and epsilon. `LLYSourceScale.lean` chooses the actual integer
scale from `Nat.log ell (n1-1)` and retains the first-rank-one case.
`LLYSourceRankValidity.lean` proves rank positivity, order and half-dimension
conditions eventually uniformly in the whole degree window.

`LLYThirdNetCardinalityUniform.lean` gives the exact vector/scalar net
product bound `exp(n*log(d)/64)`. `LLYThirdAdjointDecay.lean` proves that
the second-rank coefficient density grows at least as `(a2/2)*d^(1/4)`;
the scalar decay absorbs the selected-row loss and both nets, leaving
`exp(-n*log(d)/32)` uniformly for `C*log(n)<=d<=n/2` under the fixed
constant restrictions. `LLYThirdApproximationBudgets.lean` proves the
actual centered-adjoint mesh error fits automatically for all shifts in
`norm(zeta)<=sqrt(d)*log(log(d))`.

`LLYThirdSourceProbability.lean` gives the actual unit third-class
almost-constant adjoint bound at these ranks and scale. `LLYSourceRadius.lean`
constructs a positive radius as the minimum of the proved gradual and
third normalization allowances. At that radius the probability is at
most `n^(-A)+exp(-n*log(d)/32)`, with no separate entropy, mesh or rank
budgets assumed. These ten modules add 50 checked theorems and thirteen
definitions. This supplies one required steep-class branch. The
second-class estimate, later right-kernel exclusions, the radius exponent
and the full source smallest-value and regime assembly are still open.
Named coverage remains 23/29; all manuscript sources are unchanged.

The rare-coefficient fixed-vector input needed for the second steep
adjoint class is now proved outright. `RareBernoulliAtoms.lean` retains
the exact Bernoulli zero and single-selection masses for any finite
index type. `RareBernoulliSmallBall.lean` proves a scalar ball of radius
t/3 misses probability at least m*p/2 whenever m*p<=1/2 and each selected
coefficient has modulus at least t. `RareSmallBallTensorization.lean`
gives exp(-m*p*n/8) at squared norm threshold t^2*m*p*n/72.

`RareRowSliceSelectedAdjoint.lean` proves the exact selected-row transfer
and absorbs the sqrt(d) conditioning factor for large degree.
`RareRowSliceFullAdjoint.lean` fixes every unselected row into the
deterministic center. The actual full shifted-slice adjoint probability
is then at most exp(-m*d/16), at squared threshold t^2*m*d/72.
The ordered-gap selection is checked after every constant shift.
`RareSteepNetAdjoint.lean` uses norm threshold sqrt(m*d)/30 and charges
both literal finite-net counts in the union bound.
`RareLLYSourceFirstCoefficients.lean` discharges the rare-density premise
at the literal first rank, including rank one. The fixed-vector estimate
at the source first/second ranks holds eventually uniformly across
C*log(n)<=d<=n/2.

The second-class net must use the full first-jump scale profile.
`LLYFirstScaleEntropy.lean` proves its weighted grid scale cost is at
most 10*n1; the n1=1 cost is exactly zero. This avoids the unabsorbable
extra scale factor from charging the global maximum coordinate cap to
every first-prefix coordinate. `LLYFirstScaleCoordinateBounds.lean`
proves the actual remaining cap from every first-jump scale, including
the normalized second class. These nine modules add 32 checked theorems
and four definitions. The uniform second-class source-budget discharge, later right-kernel exclusions,
the radius exponent and full source assembly remain open. Named coverage
stays 23/29 and all manuscript sources are preserved.

The refined second-class finite net is now constructed outright.
`LayeredSparseGridNet.lean` counts an actual product of sparse grids
under vector addition. `LLYSecondSteepNet.lean` covers every normalized
actual second-class vector: ordered-prefix increments telescope, with
separate remaining-scale caps and a unit-cap residual. Canonical
truncation preserves the first/second ordered gap.

`SmallSetPowerBound.lean` proves that all coordinate sets of size at
most s number at most (n+1)^s. `LLYSecondNetEntropy.lean` retains the
exact product of layer grids. Its weighted scale cost is at most
10*n1 and its support sum at most 5*n1, both vanishing at n1=1.
The actual vector/scalar log cost is at most
5*n1*log(n+1)+(40*n1+3*(n2-1)+5)*log(d)+n*smallSetEntropy(a)
under the stated second-prefix density bound.

`LLYSecondSteepAdjointProbability.lean` proves the finite cover of the
actual normalized adjoint event, charging both net counts and the
centered-operator failure. `LLYSecondSteepNormalization.lean` checks
unit-vector normalization with B2=sqrt(n)*(6*d)^(r+1). The whole actual
second-class probability is at most n^(-A)+exp(-n1*d/32) under explicit
rare-density, conditioning, approximation and entropy budgets.
These six modules add 31 checked theorems and twelve definitions.
Uniform discharge of the second-class budgets at the literal source
ranks, later right-kernel estimates, the radius exponent and the full
source assembly remain unproved. Named coverage remains 23/29;
no manuscript source is changed and no named result is promoted.

The second steep adjoint branch now has every source budget discharged.
`LLYSecondSourceEntropy.lean` retains the literal ceiling, floor and
integer scale. The actual vector/scalar net product is at most
exp(n1*d/32), eventually uniformly for C*log(n)<=d<=n/2.
`LogLogPowerBudgets.lean` composes the logarithmic little-o bound with
the dimension logarithm. `LLYSecondApproximationBudgets.lean` fits the
spectral-window centered mesh error below sqrt(n1*d)/60. The existing
third-class source radius fits the second-class unit residual below
that same threshold.

`LLYSecondSourceProbability.lean` combines these estimates for the actual
full shifted-slice adjoint. Rank orders that cannot support the second
class are handled by its proved emptiness. `LLYSecondAdjointDecay.lean`
bounds n1*d below by a positive multiple of sqrt(n), proving that its
exponential remainder is below every polynomial rate uniformly for d<=n.
`LLYSecondSourcePolynomial.lean` gives actual second-class unit failure
probability at most n^(-A), at threshold rho_source^2/n, throughout the
spectral window norm(zeta)<=sqrt(d)*log(log(d)). It assumes C>=1920000,
0<a1<=1, a2>0, A>=0 and A+4<=9*C, and has no independent rank-fit,
rare-density, conditioning, mesh or entropy budget. Its almost-constant
subevent has the same bound.

These six modules add 25 checked theorems and one definition. Later
right-kernel estimates, remaining first/gradual source parameter budgets,
the radius exponent and full source minimum/regime assembly remain
unproved. Named coverage stays 23/29; manuscript sources are unchanged.

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


The third-class almost-constant right-kernel branch is proved in
`HypergeometricRelativeTail.lean`,
`UniformEmbeddingOccupancy.lean`,
`BlockPairOccupancy.lean`,
`SeparatedBlockPairTail.lean`,
`SeparatedBlockSliceSmallBall.lean`,
`SeparatedBlockRightAction.lean`,
`OrderedLargeTailRightAction.lean`,
`LLYThirdSteepKernelProbability.lean`,
`SeparatedBlockCoefficientDecay.lean`,
`LLYThirdSourceKernelProbability.lean`.
The exact-slice occupancy lower tail is relative to its actual mean.
Conditional unused-population sampling gives a large-low-block
separated-pair tail; direct scalar small balls then tensorize over
independent rows. The retained finite cover preserves the actual
almost-constant unit-vector condition.

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


The actual row-slice circular law is now proved in both manuscript
regimes and across the full logarithmic sparse range. Slice-only minimum
limits supply row regularization removal and bottom tails. The checked
Bernoulli full-log limit supplies vanishing determinant-zero probability,
and its negative-log tails remove the comparator ridge. Actual determinant
interlacing and common-scale cancellation give the row-slice log limit;
checked direct hermitization and variance transfer give both circular-law
regimes. Completed degree sequences and two-filter assembly supply
`main_circular_law_theorem : MainTheorem`.

Three modules add 19 checked theorems and three definitions. The named
main, lower-band and superlogarithmic conclusions are promoted only after
review against their actual source statements. Named coverage is 26/29.
The separate quantitative joint minimum estimates and literal shared-C
tensorization lemma remain unfinished. The reviewed rounded auxiliary
comparison is not used; all manuscript hashes remain unchanged.


The actual Bernoulli fresh-row scalar probability now supplies its
minimum-value reduction. Disjoint entry blocks give the independent past
and fresh-row laws. Reconstructing the sample fixes the chosen unit normal;
its shifted scalar form is bounded by the actual row distance. The proved
non-almost-constant small-ball estimate therefore gives
`C_B/sqrt(delta*d)` plus the actual leave-one-out almost-constant kernel
probability. The square minimum reduction has the bound
`kappa+(C_B/sqrt(delta*d)+eta)/delta`, with the square-adjoint and
leave-one-out almost-constant probabilities still required as inputs.

Four modules add 17 checked theorems, nine definitions and one
abbreviation. The Bernoulli almost-constant bounds, the literal joint
quantitative minimum conclusions and the tensorization statement review
remain unfinished. Named coverage stays 26/29; all manuscript hashes
are unchanged.


The actual Bernoulli gradual almost-constant branches now have checked
probability bounds. Arbitrary finite product laws have the required
one-sixteenth event-count upper tail. The original Bernoulli row law gives
exact load means and Markov bounds; restricting retained entry blocks and
currying gives the actual product row law. Uniform counting and entropy
then control all subsets at both LLY ranks. All row degrees are at least
`9*d/10` outside probability `n*exp(-d/200)`.

Variable-cardinality supports retain enough close coordinates and control
the bad-coordinate mass on the surviving rows. The checked gradual
geometry gives the actual retained norm lower bound, including the strict
first prefix. Its failure probability is at most
`E=n*exp(-d/200)+exp(-(rowLoadRate/4)*n)` under the explicit finite rank,
radius, entropy and shift budgets. Actual adjoint invariance supplies the
adjoint branch with the conjugated shift, and the retained estimate
supplies every leave-one-out kernel branch.

The full Bernoulli minimum reduction now retains only the steep adjoint
and steep leave-one-out probabilities, preserving their almost-constant
conditions. Nine modules add 42 checked theorems and 15 definitions.
The Bernoulli steep probability estimates, complete source parameter
assembly and literal quantitative joint conclusions remain unfinished.
Named coverage remains 26/29; all manuscript hashes are unchanged.


The actual Bernoulli first steep class now has its retained norm, finite
probability and literal source-parameter estimates proved. Arbitrary
finite product laws give the four-fifths lower tail. Exact mutually
exclusive selected-coordinate patterns have probability
`|L|*(d/n)*(1-d/n)^(|J|-1)`. The actual retained row law, a lower bound
on eligible rows and finite disjoint-pair entropy give the simultaneous
unique-witness event. Actual row degrees are at most `2*d` outside
probability `n*exp(-(2*log(2)-1)*d)`, and a six-degree coordinate jump
then forces a retained norm of at least
`sqrt(d)/(4*llyFirstSteepNormConstant)`.

The finite estimate also covers each omitted-row kernel. Source ceiling
ranks either equal one, making the class empty, or obey the existing
floor witness budget. The literal square-root stride, scale count and
source radius give arbitrary polynomial failure `2*n^(-A)` eventually
above an explicit absolute coefficient times `log(n)`. Source-parameter
splits and actual adjoint invariance leave only the almost-constant
second and third steep classes as probability obligations. Eight modules
add 32 checked theorems and ten definitions. The two named quantitative
joint conclusions remain open, the tensorization statement review remains
partial, and all 14 manuscript source hashes remain unchanged.

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

This milestone passed the full build (9128 jobs), the axiom audit
(12706 declarations; 6194 named theorems), all seven coverage integrity
tests and the axiom-audit rejection test. The strict completion gate
verified the mappings and correctly reported 27/29 proved and two open.


## Complete joint minimum estimates and final verification (2026-10-10)

Fourteen modules from `BernoulliRareSubset` through
`JointSmallestSingularTheorems` add 53 checked theorems, nine definitions
and one parameter structure. Actual selected-coordinate Bernoulli
small-ball bounds retain every input coefficient. Exact product splitting,
finite-type tensorization, retained entry-block restriction and the actual
shifted action supply rare and large ordered-coordinate estimates.
The mean-corrected Bernoulli net pays its fluctuating row-sum term.
Second and third normalized classes, finite-net entropy, source-rounded
ranks and radius budgets give their actual retained probabilities.
Adjoint invariance preserves the conjugated shift, and all one-row
omissions are controlled. The source minimum assembly discharges every
steep and gradual probability input of the fresh-row reduction.

A common fixed source parameter choice supplies both actual laws. The
logarithmic-degree joint target supplies both source exponent bounds and
holds at every admissible dimension after enlarging one absolute degree
constant. The superlogarithmic target has a shared polynomial exponent,
an absolute probability coefficient independent of epsilon, and a
sufficiently large dimension threshold uniform in degree and shift.
Both named targets are independently proved.

The user-approved `FINAL_STATEMENT_CORRECTIONS.patch` is applied. It makes
the corollary's sufficiently large dimension condition explicit and
replaces the false rounded T2 auxiliary comparison by the checked actual
minor-prefix convergence. Together with the separately approved
tensorization correction, this resolves the recorded statement issues.
The source-to-Lean mappings are reviewed in
[CIRCULAR_LAW_STATEMENT_REVIEW.md](CIRCULAR_LAW_STATEMENT_REVIEW.md).

Final verification passes: full build with 9142 jobs; axiom audit of
12853 project declarations, including generated helpers, and 6247 named
theorems; all seven coverage integrity tests and the axiom-rejection test;
strict completion gate with 29/29 proved and no open, partial or
statement-only results. The ledger matches all 14 TeX files and all 29
named statements. No admitted proof or added mathematical axiom is used.
The existing PDF has not been regenerated because no terminal TeX
compiler is available; the corrected TeX and formalization are current.
