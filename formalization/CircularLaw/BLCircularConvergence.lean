import CircularLaw.CircularSpatialConvergence
import CircularLaw.BLProbabilityConvergence

/-!
# Full bounded-Lipschitz convergence to the circular measure

The circle has no outer mass beyond radius one. A finite smooth disk
cover controls all bounded-Lipschitz tests, while matrix energy controls
the spectral tail in probability. No circular-law conclusion is assumed.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology ENNReal

namespace CircularLaw

theorem circular_measure_outer_tail_zero {R : ℝ} (hR : 1 < R) :
    circularMeasure.real {z : ℂ | R ≤ ‖z‖} = 0 := by
  have hAe : ∀ᵐ z : ℂ ∂circularMeasure, ¬(R ≤ ‖z‖) := by
    filter_upwards [circular_measure_ae_unit_disk] with z hz
    have hzNorm : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    linarith
  have hZero : circularMeasure {z : ℂ | R ≤ ‖z‖} = 0 := by
    simpa only [not_not] using ae_iff.mp hAe
  simp only [measureReal_def, hZero, ENNReal.toReal_zero]

theorem bl_circular_test_difference_approximation {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (f : BLTest) (φ : ℂ → ℝ) (hφ : Continuous φ)
    (hBound : ∀ z, |φ z| ≤ 2) (R η : ℝ) (hR : 1 < R) (hη : 0 ≤ η)
    (hApprox : ∀ z ∈ Metric.closedBall 0 R, |f.val z - φ z| ≤ η) :
    |(∫ z : ℂ, f.val z ∂empiricalSpectralMeasure A) -
      ∫ z : ℂ, f.val z ∂circularMeasure| ≤
      |(∫ z : ℂ, φ z ∂empiricalSpectralMeasure A) -
        ∫ z : ℂ, φ z ∂circularMeasure| + 2 * η +
      3 * (empiricalSpectralMeasure A).real {z | R ≤ ‖z‖} := by
  have hfInt : Integrable f.val circularMeasure :=
    (integrable_const 1).mono' f.2.2.continuous.aestronglyMeasurable
      (ae_of_all _ (fun z => f.2.1 z))
  have hφInt : Integrable φ circularMeasure :=
    (integrable_const 2).mono' hφ.aestronglyMeasurable (ae_of_all _ hBound)
  have hA := bl_spectral_integral_disk_approximation_bound hn A f φ hBound R η hη hApprox
  have hC := bl_integral_disk_approximation_bound circularMeasure f φ hfInt hφInt
    hBound R η hη hApprox
  rw [circular_measure_outer_tail_zero hR, mul_zero, add_zero] at hC
  have h1 := abs_sub_le (∫ z : ℂ, f.val z ∂empiricalSpectralMeasure A)
    (∫ z : ℂ, φ z ∂empiricalSpectralMeasure A) (∫ z : ℂ, f.val z ∂circularMeasure)
  have h2 := abs_sub_le (∫ z : ℂ, φ z ∂empiricalSpectralMeasure A)
    (∫ z : ℂ, φ z ∂circularMeasure) (∫ z : ℂ, f.val z ∂circularMeasure)
  rw [abs_sub_comm (∫ z : ℂ, φ z ∂circularMeasure)] at h2
  linarith

theorem bounded_lipschitz_circular_distance_finite_test_bound {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (s : Finset (ℂ → ℝ))
    (hContinuous : ∀ φ ∈ s, Continuous φ) (hBounds : ∀ φ ∈ s, ∀ z, |φ z| ≤ 2)
    (R η δ τ : ℝ) (hR : 1 < R) (hη : 0 ≤ η)
    (hCover : ∀ f : BLTest, ∃ φ ∈ s, ∀ z ∈ Metric.closedBall 0 R, |f.val z - φ z| ≤ η)
    (hTests : ∀ φ ∈ s, |(∫ z : ℂ, φ z ∂empiricalSpectralMeasure A) -
      ∫ z : ℂ, φ z ∂circularMeasure| ≤ δ)
    (hTail : (empiricalSpectralMeasure A).real {z | R ≤ ‖z‖} ≤ τ) :
    boundedLipschitzDistance (empiricalSpectralMeasure A) circularMeasure ≤
      ENNReal.ofReal (δ + 2 * η + 3 * τ) := by
  apply iSup_le
  intro f
  obtain ⟨φ, hφs, hApprox⟩ := hCover f
  apply ENNReal.ofReal_le_ofReal
  have h := bl_circular_test_difference_approximation hn A f φ (hContinuous φ hφs)
    (hBounds φ hφs) R η hR hη hApprox
  linarith [hTests φ hφs]

theorem bounded_lipschitz_circular_convergence_of_compact_C2_tests {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : ∀ n, Ω n → Matrix (Fin n) (Fin n) ℂ)
    (hEnergy : VaryingBoundedInProbability μ (fun n ω => squareMatrixEnergy (A n ω) / n))
    (hTest : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      VaryingConvergesInProbability μ (fun n ω =>
        (∫ z : ℂ, φ z ∂empiricalSpectralMeasure (A n ω)) -
          ∫ z : ℂ, φ z ∂circularMeasure) 0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (A n ω)) circularMeasure})
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨M, hM, hEnergyProb⟩ := hEnergy (δ / 2) (by positivity)
  let η : ℝ := min (ε / 16) (1 / 2)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηSmall : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hηE : η ≤ ε / 16 := min_le_left _ _
  let τ : ℝ := ε / 24
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let R : ℝ := Real.sqrt (M / τ) + 2
  have hR : 1 < R := by dsimp [R]; linarith [Real.sqrt_nonneg (M / τ)]
  have hRPos : 0 < R := zero_lt_one.trans hR
  have hRatio : M / R ^ 2 < τ := by
    have hMT : 0 < M / τ := div_pos hM hτ
    have hSq : M / τ < R ^ 2 := by
      dsimp [R]
      nlinarith [Real.sq_sqrt hMT.le, Real.sqrt_nonneg (M / τ)]
    have h := mul_lt_mul_of_pos_left hSq hτ
    rw [mul_div_cancel₀ M hτ.ne'] at h
    exact (div_lt_iff₀ (sq_pos_of_pos hRPos)).mpr h
  obtain ⟨s, hSmooth, hCover⟩ := bltest_finite_smooth_disk_cover R hη hηSmall
  let badTests : ∀ n, Set (Ω n) := fun n => {ω | ∃ φ ∈ s, ε / 4 <
    |(∫ z : ℂ, φ z ∂empiricalSpectralMeasure (A n ω)) - ∫ z : ℂ, φ z ∂circularMeasure|}
  have hTestProb : Tendsto (fun n => (μ n).real (badTests n)) atTop (𝓝 0) := by
    apply varying_finite_test_exceedance_tendsto_zero μ s
      (fun φ n ω => (∫ z : ℂ, φ z ∂empiricalSpectralMeasure (A n ω)) -
        ∫ z : ℂ, φ z ∂circularMeasure) _ (by positivity)
    intro φ hφ
    exact hTest φ (hSmooth φ hφ).1 (hSmooth φ hφ).2.1
  have hTestsSmall : ∀ᶠ n in atTop, (μ n).real (badTests n) < δ / 2 :=
    hTestProb.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ / 2))
  filter_upwards [hEnergyProb, hTestsSmall, eventually_gt_atTop 0] with n hnEnergy hnTests hn
  let bad : Set (Ω n) := {ω | M < |squareMatrixEnergy (A n ω) / n|}
  have hSubset : {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (A n ω)) circularMeasure} ⊆
        bad ∪ badTests n := by
    intro ω hω
    by_contra hNot
    have hGood : ω ∉ bad ∧ ω ∉ badTests n := by simpa only [mem_union, not_or] using hNot
    have hEA : squareMatrixEnergy (A n ω) / n ≤ M :=
      (le_abs_self _).trans (le_of_not_gt hGood.1)
    have hTail : (empiricalSpectralMeasure (A n ω)).real {z | R ≤ ‖z‖} ≤ τ :=
      (empirical_spectral_tail_bound hn (A n ω) hRPos).trans
        ((div_le_div_of_nonneg_right hEA (sq_nonneg R)).trans hRatio.le)
    have hTestBounds : ∀ φ ∈ s,
        |(∫ z : ℂ, φ z ∂empiricalSpectralMeasure (A n ω)) -
          ∫ z : ℂ, φ z ∂circularMeasure| ≤ ε / 4 := by
      intro φ hφ
      by_contra h
      exact hGood.2 ⟨φ, hφ, lt_of_not_ge h⟩
    have hDist := bounded_lipschitz_circular_distance_finite_test_bound hn (A n ω) s
      (fun φ hφ => (hSmooth φ hφ).1.continuous) (fun φ hφ => (hSmooth φ hφ).2.2)
      R η (ε / 4) τ hR hη.le
      (fun f => by
        obtain ⟨φ, hφ, hApprox⟩ := hCover f
        exact ⟨φ, hφ, fun z hz => (hApprox z hz).le⟩) hTestBounds hTail
    have hBudget : ε / 4 + 2 * η + 3 * τ ≤ ε := by dsimp [τ]; linarith
    exact not_lt_of_ge (hDist.trans (ENNReal.ofReal_le_ofReal hBudget)) hω
  have hProbability : (μ n).real {ω | ENNReal.ofReal ε <
      boundedLipschitzDistance (empiricalSpectralMeasure (A n ω)) circularMeasure} < δ := by
    have h := (measureReal_mono (μ := μ n) hSubset).trans (measureReal_union_le _ _)
    dsimp [bad] at h
    linarith
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] using hProbability

end CircularLaw
