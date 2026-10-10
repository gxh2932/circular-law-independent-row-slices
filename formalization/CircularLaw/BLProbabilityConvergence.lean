import CircularLaw.BLFiniteSpectralBound
import CircularLaw.VaryingFiniteTestProbability

/-!
# Full bounded-Lipschitz convergence from compact C2 tests

The finite smooth test family is constructed before taking probability
limits. Energy bounds control both outer spectral tails. The finite
probability union then controls the actual supremum over every BL test.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology ENNReal

namespace CircularLaw

theorem bounded_lipschitz_convergence_of_compact_C2_tests {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hEnergyA : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hEnergyB : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (B n ω) / n))
    (hTest : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      VaryingConvergesInProbability μ (fun n ω =>
        (∫ z : ℂ, φ z ∂empiricalSpectralMeasure (A n ω)) -
          ∫ z : ℂ, φ z ∂empiricalSpectralMeasure (B n ω)) 0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (A n ω))
        (empiricalSpectralMeasure (B n ω))}) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨MA, hMA, hEnergyProbA⟩ := hEnergyA (δ / 4) (by positivity)
  obtain ⟨MB, hMB, hEnergyProbB⟩ := hEnergyB (δ / 4) (by positivity)
  let M : ℝ := max MA MB
  have hM : 0 < M := hMA.trans_le (le_max_left _ _)
  let η : ℝ := min (ε / 16) (1 / 2)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηSmall : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hηE : η ≤ ε / 16 := min_le_left _ _
  let τ : ℝ := ε / 24
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let R : ℝ := Real.sqrt (M / τ) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hRatio : M / R ^ 2 < τ := by
    have hMT : 0 < M / τ := div_pos hM hτ
    have hSq : M / τ < R ^ 2 := by
      dsimp [R]
      nlinarith [Real.sq_sqrt hMT.le, Real.sqrt_nonneg (M / τ)]
    have h := mul_lt_mul_of_pos_left hSq hτ
    rw [mul_div_cancel₀ M hτ.ne'] at h
    exact (div_lt_iff₀ (sq_pos_of_pos hR)).mpr h
  obtain ⟨s, hSmooth, hCover⟩ := bltest_finite_smooth_disk_cover R hη hηSmall
  let badTests : ∀ n, Set (Ω n) := fun n => {ω | ∃ φ ∈ s, ε / 4 <
    |(∫ z : ℂ, φ z ∂empiricalSpectralMeasure (A n ω)) -
      ∫ z : ℂ, φ z ∂empiricalSpectralMeasure (B n ω)|}
  have hTestProb : Tendsto (fun n => (μ n).real (badTests n)) atTop (𝓝 0) := by
    apply varying_finite_test_exceedance_tendsto_zero μ s
      (fun φ n ω => (∫ z : ℂ, φ z ∂empiricalSpectralMeasure (A n ω)) -
        ∫ z : ℂ, φ z ∂empiricalSpectralMeasure (B n ω)) _ (by positivity)
    intro φ hφ
    exact hTest φ (hSmooth φ hφ).1 (hSmooth φ hφ).2.1
  have hTestsSmall : ∀ᶠ n in atTop, (μ n).real (badTests n) < δ / 2 :=
    hTestProb.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ / 2))
  filter_upwards [hEnergyProbA, hEnergyProbB, hTestsSmall, eventually_gt_atTop 0]
    with n hnA hnB hnTests hn
  let badA : Set (Ω n) := {ω | MA < |squareMatrixEnergy (A n ω) / n|}
  let badB : Set (Ω n) := {ω | MB < |squareMatrixEnergy (B n ω) / n|}
  have hSubset : {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (A n ω))
        (empiricalSpectralMeasure (B n ω))} ⊆ (badA ∪ badB) ∪ badTests n := by
    intro ω hω
    by_contra hNot
    have hGood : ω ∉ badA ∧ ω ∉ badB ∧ ω ∉ badTests n := by
      simpa only [mem_union, not_or, and_assoc] using hNot
    have hEA : squareMatrixEnergy (A n ω) / n ≤ M :=
      (le_abs_self _).trans ((le_of_not_gt hGood.1).trans (le_max_left _ _))
    have hEB : squareMatrixEnergy (B n ω) / n ≤ M :=
      (le_abs_self _).trans ((le_of_not_gt hGood.2.1).trans (le_max_right _ _))
    have hTailA : (empiricalSpectralMeasure (A n ω)).real {z | R ≤ ‖z‖} ≤ τ :=
      (empirical_spectral_tail_bound hn (A n ω) hR).trans
        ((div_le_div_of_nonneg_right hEA (sq_nonneg R)).trans hRatio.le)
    have hTailB : (empiricalSpectralMeasure (B n ω)).real {z | R ≤ ‖z‖} ≤ τ :=
      (empirical_spectral_tail_bound hn (B n ω) hR).trans
        ((div_le_div_of_nonneg_right hEB (sq_nonneg R)).trans hRatio.le)
    have hTestBounds : ∀ φ ∈ s,
        |(∫ z : ℂ, φ z ∂empiricalSpectralMeasure (A n ω)) -
          ∫ z : ℂ, φ z ∂empiricalSpectralMeasure (B n ω)| ≤ ε / 4 := by
      intro φ hφ
      by_contra h
      exact hGood.2.2 ⟨φ, hφ, lt_of_not_ge h⟩
    have hDist := bounded_lipschitz_distance_finite_test_bound hn (A n ω) (B n ω) s
      (fun φ hφ => (hSmooth φ hφ).2.2) R η (ε / 4) τ hη.le
      (fun f => by
        obtain ⟨φ, hφ, hApprox⟩ := hCover f
        exact ⟨φ, hφ, fun z hz => (hApprox z hz).le⟩)
      hTestBounds hTailA hTailB
    have hBudget : ε / 4 + 2 * η + 6 * τ ≤ ε := by dsimp [τ]; linarith
    exact not_lt_of_ge (hDist.trans (ENNReal.ofReal_le_ofReal hBudget)) hω
  have hUnion : (μ n).real ((badA ∪ badB) ∪ badTests n) ≤
      (μ n).real badA + (μ n).real badB + (μ n).real (badTests n) :=
    (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
  have hProbability : (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (A n ω))
        (empiricalSpectralMeasure (B n ω))} < δ := by
    have h := (measureReal_mono hSubset).trans hUnion
    dsimp [badA, badB] at h
    linarith
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] using hProbability

end CircularLaw
