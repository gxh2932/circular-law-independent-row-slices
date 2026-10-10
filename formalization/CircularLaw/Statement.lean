import CircularLaw.RowSlice
import CircularLaw.FiniteProbability
import CircularLaw.Assembly

/-!
# The full circular-law target

`MainTheorem` is the target proposition, proved by
`main_circular_law_theorem` in `CircularLawProvedRegimes.lean`.
`convergence_of_regime_tail_bounds` gives the final assembly step from
both regime estimates.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace CircularLaw

/-- Normalization from Theorem 1.1 of the manuscript. -/
def normalizedMatrix {n d : ℕ} (s : RowSliceMatrix n d) : Matrix (Fin n) (Fin n) ℂ :=
  (↑(Real.sqrt (bulkScaleSq n d)) : ℂ)⁻¹ • sliceMatrix s

/-- The empirical spectral measure counts characteristic roots with algebraic
multiplicity. In dimension zero this definition is the zero measure. -/
def empiricalSpectralMeasure {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Measure ℂ :=
  (n : ℝ≥0∞)⁻¹ • (A.charpoly.roots.map fun z => Measure.dirac z).sum

/-- Uniform area measure on the complex unit disk. -/
def circularMeasure : Measure ℂ :=
  (ENNReal.ofReal Real.pi)⁻¹ • volume.restrict (Metric.closedBall (0 : ℂ) 1)

theorem circularMeasure_univ : circularMeasure Set.univ = 1 := by
  simp only [circularMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Complex.volume_closedBall, ENNReal.ofReal_one, one_pow, one_mul,
    ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast NNReal.pi_pos.ne') ENNReal.coe_ne_top

/-- Every positive-dimensional ESD has total mass one, including repeated
eigenvalues. This checks the normalization in the target statement. -/
theorem empiricalSpectralMeasure_univ {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) : empiricalSpectralMeasure A Set.univ = 1 := by
  have hmass (roots : Multiset ℂ) :
      ((roots.map fun z => Measure.dirac z).sum : Measure ℂ) Set.univ = roots.card := by
    induction roots using Multiset.induction_on with
    | empty => simp
    | @cons z roots ih => simp [ih, add_comm]
  have hroots : A.charpoly.roots.card = n := by
    rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots]
    simp
  have hn' : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [empiricalSpectralMeasure, Measure.smul_apply, smul_eq_mul, hmass, hroots]
  exact ENNReal.inv_mul_cancel hn' (by simp)

/-- Bounded, real-valued, 1-Lipschitz test functions. -/
def BLTest := {f : ℂ → ℝ // (∀ z, |f z| ≤ 1) ∧ LipschitzWith 1 f}

/-- The bounded-Lipschitz distance, with an extended nonnegative value so the
supremum is well-defined without extra boundedness assumptions. -/
def boundedLipschitzDistance (μ ν : Measure ℂ) : ℝ≥0∞ :=
  ⨆ f : BLTest, ENNReal.ofReal |(∫ z, f.val z ∂μ) - ∫ z, f.val z ∂ν|

/-- Probability that the normalized ESD is farther than `ε` from the circular
law. The uniform matrix law assigns equal weight to every row tuple. -/
def circularTail (d : ℕ → ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  uniformProbability fun s : RowSliceMatrix n (d n) =>
    ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (normalizedMatrix s)) circularMeasure

/-- Weak convergence of the random ESD to the circular law in probability. -/
def CircularConvergence (d : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (circularTail d ε) atTop (𝓝 0)

/-- The degree hypothesis `d=o(n)`. -/
def SparseDegrees (d : ℕ → ℕ) : Prop :=
  Tendsto (fun n : ℕ => (d n : ℝ) / n) atTop (𝓝 0)

/-- The eventual logarithmic lower bound. -/
def LogLowerBound (C : ℝ) (d : ℕ → ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop, C * Real.log n ≤ (d n : ℝ)

/-- The main hypotheses eventually describe nonempty slices with a strictly
positive bulk scale, so the limiting assertion cannot use empty sample spaces. -/
theorem eventually_valid_degrees {C : ℝ} {d : ℕ → ℕ} (hC : 0 < C)
    (hlog : LogLowerBound C d) (hsparse : SparseDegrees d) :
    ∀ᶠ n : ℕ in atTop, 0 < d n ∧ d n < n := by
  have hratio : ∀ᶠ n : ℕ in atTop, (d n : ℝ) / n < 1 :=
    hsparse.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlog, hratio, eventually_ge_atTop 2] with n hlogn hrat hn
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hdreal : (0 : ℝ) < d n :=
    lt_of_lt_of_le (mul_pos hC (Real.log_pos hnreal)) hlogn
  constructor
  · exact_mod_cast hdreal
  · have := (div_lt_one (lt_trans zero_lt_one hnreal)).mp hrat
    exact_mod_cast this

/-- Full statement of the manuscript's main theorem. Its checked proof is
`main_circular_law_theorem` in `CircularLawProvedRegimes.lean`. -/
def MainTheorem : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ d : ℕ → ℕ, LogLowerBound C d → SparseDegrees d → CircularConvergence d

/-- Checked final assembly conditional on actual tail bounds in both regimes. -/
theorem convergence_of_regime_tail_bounds (d : ℕ → ℕ)
    (hlow : ∀ ε : ℝ, 0 < ε →
      Tendsto (circularTail d ε) (atTop ⊓ 𝓟 (lowerRegime d)) (𝓝 0))
    (hhigh : ∀ ε : ℝ, 0 < ε →
      Tendsto (circularTail d ε) (atTop ⊓ 𝓟 (lowerRegime d)ᶜ) (𝓝 0)) :
    CircularConvergence d := by
  intro ε hε
  exact tail_tendsto_of_degree_regimes d _ (hlow ε hε) (hhigh ε hε)

end CircularLaw
