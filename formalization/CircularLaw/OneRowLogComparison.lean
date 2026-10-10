import CircularLaw.OneRowLogRates
import CircularLaw.OneRowLogScale
import CircularLaw.FiniteLawTransport

/-!
# Complete one-row logarithmic comparison

This uses the literal positive contraction, trace bound and Bernoulli
mean. The slice and Bernoulli rows may be coupled arbitrarily on any
probability space. Their exact marginal laws, rather than independence
of the two rows, supply every moment and tail estimate.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory
open scoped NNReal ENNReal

namespace CircularLaw

theorem one_row_log_comparison {Ω : Type*} [MeasurableSpace Ω]
    {n d r : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsPositiveMatrixContraction P)
    (hTrace : (r : ℝ) + 1 ≤ P.trace.re) (η : ℝ) (hη : 0 < η) (u : EuclideanSpace ℂ (Fin n))
    (hQ : 1 ≤ rowLogComparisonQ n d r)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → RowSlice n d) (hX : Measurable X) (hXlaw : μ.map X = rowSliceLaw n d)
    (Y : Ω → (Fin n → Bool)) (hY : Measurable Y)
    (hYlaw : μ.map Y = bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
      (rowBernoulliParameter_le_one (by omega) hdn)) (U : ℝ)
    (hU : ∀ᵐ ω ∂μ, regularizedDistance P η u (rowSliceEuclideanRow (X ω)) ≤ U ∧
      regularizedDistance P η u (bernoulliCubeVector (Y ω)) ≤ U) :
    (∫ ω, |Real.log (regularizedDistance P η u (rowSliceEuclideanRow (X ω))) -
      Real.log (regularizedDistance P η u (bernoulliCubeVector (Y ω)))| ∂μ) ≤
      9216 * Real.sqrt (rowLogDegree d / rowLogComparisonQ n d r) +
        (2 * rowDistanceTailConstant) * Real.sqrt (d : ℝ) * Real.log (U / η) *
          Real.exp (-(1 / 262144) * rowLogComparisonQ n d r) := by
  letI := rowSliceLaw_probability hdn
  let f₀ := fun s : RowSlice n d => regularizedDistance P η u (rowSliceEuclideanRow s)
  let g₀ := fun x : Fin n → Bool => regularizedDistance P η u (bernoulliCubeVector x)
  let f := fun ω => f₀ (X ω)
  let g := fun ω => g₀ (Y ω)
  let m := regularizedDistanceMean P η u (rowBernoulliParameter n d)
    (rowBernoulliParameter_le_one (by omega) hdn)
  have hf : Measurable f := (measurable_of_countable f₀).comp hX
  have hg : Measurable g := (measurable_of_countable g₀).comp hY
  have hBounds : ∀ᵐ ω ∂μ, η ≤ f ω ∧ f ω ≤ U ∧ η ≤ g ω ∧ g ω ≤ U := by
    filter_upwards [hU] with ω hω
    exact ⟨regularizedDistance_ge_eta hP.1 η u _, hω.1,
      regularizedDistance_ge_eta hP.1 η u _, hω.2⟩
  have hηU : η ≤ U := by
    obtain ⟨ω, hω⟩ := hBounds.exists
    exact hω.1.trans hω.2.1
  have hfInt : Integrable (fun ω => |f ω - m|) μ :=
    finite_law_integrable_comp hX hXlaw (fun s => |f₀ s - m|)
  have hgInt : Integrable (fun ω => |g ω - m|) μ :=
    finite_law_integrable_comp hY hYlaw (fun x => |g₀ x - m|)
  have hfMoment : (∫ ω, |f ω - m| ∂μ) ≤ 288 * Real.sqrt (rowLogDegree d) := by
    change (∫ ω, (fun s => |f₀ s - m|) (X ω) ∂μ) ≤ _
    rw [finite_law_integral_comp hX hXlaw (fun s => |f₀ s - m|)]
    exact regularizedDistance_slice_absolute_moment hd hdn hP η u
  have hgMoment : (∫ ω, |g ω - m| ∂μ) ≤ 288 * Real.sqrt (rowLogDegree d) := by
    change (∫ ω, (fun x => |g₀ x - m|) (Y ω) ∂μ) ≤ _
    rw [finite_law_integral_comp hY hYlaw (fun x => |g₀ x - m|)]
    exact regularizedDistance_bernoulli_absolute_moment hd hdn hP η u
  have hfTail (t : ℝ) (ht : 0 < t) : μ.real {ω | t ≤ |f ω - m|} ≤
      (rowDistanceTailConstant * Real.sqrt (d : ℝ)) * Real.exp (-(1 / 1024) * t ^ 2) := by
    change μ.real {ω | (fun s => t ≤ |f₀ s - m|) (X ω)} ≤ _
    rw [finite_law_event_real hX hXlaw (fun s => t ≤ |f₀ s - m|)]
    simpa only [f₀, m, rowDistanceTailConstant, mul_assoc] using
      regularizedDistance_slice_mean_tail hd hdn hP η u ht
  have hgTail (t : ℝ) (ht : 0 < t) : μ.real {ω | t ≤ |g ω - m|} ≤
      (rowDistanceTailConstant * Real.sqrt (d : ℝ)) * Real.exp (-(1 / 1024) * t ^ 2) := by
    change μ.real {ω | (fun x => t ≤ |g₀ x - m|) (Y ω)} ≤ _
    rw [finite_law_event_real hY hYlaw (fun x => t ≤ |g₀ x - m|)]
    exact regularizedDistance_bernoulli_sqrt_degree_tail hd hdn hP η u ht
  exact one_row_log_bound_of_centered_tails μ hf hg hη hηU hd hQ
    (regularizedDistanceMean_ge_sqrt_codimension_eighth hd hdn hP hTrace η u hQ)
    hBounds hfInt hgInt hfMoment hgMoment hfTail hgTail

/-- The literal source statement, with arbitrary codimension `r<n`, exact
    row laws and upper bound holding almost surely on any coupling. -/
def OneRowLogComparisonLemma : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (n d r : ℕ) (hd : 0 < d) (hdn : d ≤ n), r < n →
    ∀ (P : Matrix (Fin n) (Fin n) ℂ), IsPositiveMatrixContraction P →
    (r : ℝ) + 1 ≤ P.trace.re →
    ∀ (η : ℝ), 0 < η → ∀ (u : EuclideanSpace ℂ (Fin n)),
    1 ≤ rowLogComparisonQ n d r →
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (X : Ω → RowSlice n d), Measurable X → μ.map X = rowSliceLaw n d →
    ∀ (Y : Ω → (Fin n → Bool)), Measurable Y →
      μ.map Y = bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
        (rowBernoulliParameter_le_one (show 0 < n by omega) hdn) →
    ∀ (U : ℝ),
      (∀ᵐ ω ∂μ, regularizedDistance P η u (rowSliceEuclideanRow (X ω)) ≤ U ∧
        regularizedDistance P η u (bernoulliCubeVector (Y ω)) ≤ U) →
      (∫ ω, |Real.log (regularizedDistance P η u (rowSliceEuclideanRow (X ω))) -
        Real.log (regularizedDistance P η u (bernoulliCubeVector (Y ω)))| ∂μ) ≤
        C * Real.sqrt (Real.log (Real.exp 1 * (d : ℝ)) / rowLogComparisonQ n d r) +
          C * Real.sqrt (d : ℝ) * Real.log (U / η) * Real.exp (-c * rowLogComparisonQ n d r)

theorem one_row_log_comparison_lemma : OneRowLogComparisonLemma := by
  refine ⟨10000 + 2 * rowDistanceTailConstant, 1 / 262144, ?_, by norm_num, ?_⟩
  · dsimp [rowDistanceTailConstant]
    positivity
  · intro n d r hd hdn _hr P hP hTrace η hη u hQ Ω _ μ hμ X hX hXlaw Y hY hYlaw U hU
    letI := hμ
    have h := one_row_log_comparison hd hdn hP hTrace η hη u hQ μ X hX hXlaw Y hY hYlaw U hU
    apply h.trans
    have hδ : 0 ≤ Real.log (U / η) := by
      obtain ⟨ω, hω⟩ := hU.exists
      have hηU := (regularizedDistance_ge_eta hP.1 η u (rowSliceEuclideanRow (X ω))).trans hω.1
      exact Real.log_nonneg ((le_div_iff₀ hη).mpr (by simpa only [one_mul] using hηU))
    have hPref : 0 ≤ rowDistanceTailConstant := by dsimp [rowDistanceTailConstant]; positivity
    have hGood := mul_le_mul_of_nonneg_right
      (show (9216 : ℝ) ≤ 10000 + 2 * rowDistanceTailConstant from by linarith)
      (Real.sqrt_nonneg (rowLogDegree d / rowLogComparisonQ n d r))
    have hBad := mul_le_mul_of_nonneg_right
      (show 2 * rowDistanceTailConstant ≤ 10000 + 2 * rowDistanceTailConstant from by linarith)
      (show 0 ≤ Real.sqrt (d : ℝ) * Real.log (U / η) * Real.exp (-(1 / 262144) * rowLogComparisonQ n d r)
        from by positivity)
    change _ ≤ (10000 + 2 * rowDistanceTailConstant) * Real.sqrt (rowLogDegree d / rowLogComparisonQ n d r) + _
    nlinarith

end CircularLaw
