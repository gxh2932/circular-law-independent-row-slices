import CircularLaw.SteepNetFit
import CircularLaw.SteepNetProbabilityRates

/-!
# Uniform source T1 and T2 kernel exclusions

Actual net counts and checked equal-block estimates are combined with
the separate full-matrix witness failures. Both codimensions and all
deterministic retained sets share one threshold. Spectral shifts range
over the fixed source window; the exponential rates are independent of
that window and of the degree-band parameter.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def sourceT1KernelRate (cw : ℝ) : ℝ :=
  min (binomialHalfRate / 4) (equalBlockRateConstant cw / 2) / 2

def sourceT2KernelRate (cw : ℝ) : ℝ :=
  min (binomialHalfRate / 1600) (equalBlockRateConstant cw / 4800) / 2

theorem sourceT1KernelRate_pos {cw : ℝ} (hcw : 0 < cw) : 0 < sourceT1KernelRate cw := by
  unfold sourceT1KernelRate
  exact div_pos (lt_min (div_pos binomialHalfRate_pos (by norm_num))
    (div_pos (equalBlockRateConstant_pos hcw) (by norm_num))) (by norm_num)

theorem sourceT2KernelRate_pos {cw : ℝ} (hcw : 0 < cw) : 0 < sourceT2KernelRate cw := by
  unfold sourceT2KernelRate
  exact div_pos (lt_min (div_pos binomialHalfRate_pos (by norm_num))
    (div_pos (equalBlockRateConstant_pos hcw) (by norm_num))) (by norm_num)

theorem source_kernel_retained_half {n d L : ℕ} (h : SourceKernelConditions n d)
    (hL : IsKernelCodimension n d L) (I : Finset (Fin n)) (hI : I.card = n - L) :
    (n : ℝ) / 2 ≤ I.card := by
  have hd : 0 < d := (source_kernel_dimension_twice_degree h).2.1
  have hPower := Nat.pow_le_pow_right hd (by decide : 3 ≤ 4)
  have hCube : 4 * d ^ 3 ≤ n := (Nat.mul_le_mul_left 4 hPower).trans h.dimension_fourth
  have hRows := kernelCodimension_retained_card (by have hLarge := h.degree_large; omega : 5 ≤ d) hCube hL I hI
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem eventually_source_shifted_T1_kernel_probability_uniform {C cw Z₀ : ℝ}
    (hC : 0 < C) (hcw : 0 < cw) (hcwSmall : cw ≤ 1 / 4) (hZ : 0 ≤ Z₀) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
          uniformProbability (fun rows : RowSliceMatrix n d =>
            ∃ v ∈ sourceShiftedT1 n d L, (retainedShiftedMatrix I ζ rows).mulVec v = 0) ≤
              Real.exp (-sourceT1KernelRate cw * n / Real.sqrt d) := by
  have hr := equalBlockRateConstant_pos hcw
  have hMin : 0 < min (binomialHalfRate / 4) (equalBlockRateConstant cw / 2) :=
    lt_min (div_pos binomialHalfRate_pos (by norm_num)) (by positivity)
  have hDegree : ∀ᶠ d : ℕ in atTop,
      14 * Real.log (d : ℝ) ≤ equalBlockRateConstant cw * Real.rpow (d : ℝ) (1 / 6) ∧
      8 * (1 + (3 / 2 : ℝ) * Real.log d) ≤ binomialHalfRate * d ∧
      2 * Real.log 2 / min (binomialHalfRate / 4) (equalBlockRateConstant cw / 2) ≤ (d : ℝ) ∧
      4 * d ≤ steepStride d ^ 3 := by
    filter_upwards [eventually_steep_net_T1_entropy hr, eventually_firstSteepScale_entropy,
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop).eventually_ge_atTop _,
      eventually_steepStride_cubic] with d hEntropy hWitness hLarge hCubic
    exact ⟨hEntropy, hWitness, hLarge, hCubic⟩
  filter_upwards [eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_source_steep_net_fit_uniform (a₃ := 1 / 4) (by norm_num) (by norm_num) hcw hC hZ σ,
    eventually_source_steep_net_cardinality_uniform (a₃ := 1 / 4) (by norm_num) (by norm_num) hC σ,
    eventually_degree_property_uniform hC hDegree] with n hConditions hFits hCounts hDegree
  intro d hBand L hL I hI ζ hShift
  have h := hConditions d hBand.1 hBand.2
  have hFit := hFits d hBand
  have hD := hDegree d hBand.1
  have hd : 0 < d := (source_kernel_dimension_twice_degree h).2.1
  have hdn : d ≤ n := by have hN := hFit.dimension; omega
  have hProbability := source_shifted_T1_kernel_finite_probability h hL hD.2.2.2 hdn hZ hcw
    hFit.first_ranks hFit.first_fit hFit.first_radius I ζ hShift
  have hWitness := firstSteepScale_witness_failure h.degree_large h.dimension_root I
    (source_kernel_retained_half h hL I hI) hcwSmall hD.2.1
  have hNet := steep_net_T1_probability_absorbed hd hr hD.1 (hCounts d hBand).1
  have hRoot : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hDensity : (d : ℝ) ≤ (n : ℝ) / Real.sqrt d := (le_div_iff₀ hRoot).mpr h.dimension_root
  have hLarge : 2 * Real.log 2 ≤ min (binomialHalfRate / 4) (equalBlockRateConstant cw / 2) *
      ((n : ℝ) / Real.sqrt d) := by
    have hDScaled := (div_le_iff₀ hMin).mp hD.2.2.1
    have hNScaled := mul_le_mul_of_nonneg_left hDensity hMin.le
    nlinarith
  have hSum := two_exponential_rates_absorbed (by positivity : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt d) hLarge
  apply hProbability.trans
  apply (add_le_add hWitness hNet).trans
  simpa only [sourceT1KernelRate, mul_div_assoc] using hSum

theorem eventually_source_shifted_T2_kernel_probability_uniform {C a₃ cw Z₀ : ℝ}
    (hC : 0 < C) (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2)
    (hcw : 0 < cw) (hcwSmall : cw ≤ 1 / 4)
    (haSmall : 7 * a₃ ≤ equalBlockRateConstant cw / 4800) (hZ : 0 ≤ Z₀) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
          uniformProbability (fun rows : RowSliceMatrix n d =>
            ∃ v ∈ sourceShiftedT2 n d L a₃, (retainedShiftedMatrix I ζ rows).mulVec v = 0) ≤
              Real.exp (-sourceT2KernelRate cw * n) := by
  have hr := equalBlockRateConstant_pos hcw
  have hMin : 0 < min (binomialHalfRate / 1600) (equalBlockRateConstant cw / 4800) :=
    lt_min (div_pos binomialHalfRate_pos (by norm_num)) (by positivity)
  have hDegree : ∀ᶠ d : ℕ in atTop,
      max 1 (6 * Real.log 2) ≤ Real.log (d : ℝ) ∧
      8 * Real.log (400 * Real.exp 1 * d) ≤ binomialHalfRate * d ∧
      2 * Real.log 2 / min (binomialHalfRate / 1600) (equalBlockRateConstant cw / 4800) ≤ (d : ℝ) ∧
      4 * d ≤ steepStride d ^ 3 := by
    filter_upwards [(Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop _,
      eventually_witness_degree_entropy,
      (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop).eventually_ge_atTop _,
      eventually_steepStride_cubic] with d hLog hWitness hLarge hCubic
    exact ⟨hLog, hWitness.2, hLarge, hCubic⟩
  filter_upwards [eventually_source_kernel_conditions_uniform hC (1 + σ),
    eventually_source_steep_net_fit_uniform ha haHalf hcw hC hZ σ,
    eventually_source_steep_net_cardinality_uniform ha (by linarith : a₃ ≤ 1) hC σ,
    eventually_degree_property_uniform hC hDegree] with n hConditions hFits hCounts hDegree
  intro d hBand L hL I hI ζ hShift
  have h := hConditions d hBand.1 hBand.2
  have hFit := hFits d hBand
  have hD := hDegree d hBand.1
  have hd : 0 < d := (source_kernel_dimension_twice_degree h).2.1
  have hProbability := source_shifted_T2_kernel_finite_probability ha (by linarith : a₃ ≤ 1)
    hFit.third_size h hL hD.2.2.2 hFit.dimension hZ hcw hFit.second_ranks
    hFit.second_fit hFit.large_blocks hFit.second_radius I ζ hShift
  have hWitness := equalBlockScale_witness_failure hd hFit.dimension I
    (source_kernel_retained_half h hL I hI) hcwSmall hD.2.1
  have hLogOne : 1 ≤ Real.log (d : ℝ) := (le_max_left _ _).trans hD.1
  have hLogLarge : 6 * Real.log 2 ≤ Real.log (d : ℝ) := (le_max_right _ _).trans hD.1
  have hNet := steep_net_T2_probability_absorbed hd hFit.dimension ha.le hr haSmall
    (by linarith : 0 ≤ Real.log (d : ℝ)) hLogLarge (hCounts d hBand).2
  have hNetBound : Real.exp (-(equalBlockRateConstant cw / 4800) * n * Real.log (d : ℝ)) ≤
      Real.exp (-(equalBlockRateConstant cw / 4800) * n) := by
    apply Real.exp_le_exp.mpr
    have hScaled := mul_le_mul_of_nonneg_left hLogOne
      (by positivity : (0 : ℝ) ≤ (equalBlockRateConstant cw / 4800) * n)
    nlinarith
  have hLarge : 2 * Real.log 2 ≤ min (binomialHalfRate / 1600) (equalBlockRateConstant cw / 4800) * (n : ℝ) := by
    have hDScaled := (div_le_iff₀ hMin).mp hD.2.2.1
    have hdn : (d : ℝ) ≤ n := by exact_mod_cast (by have hN := hFit.dimension; omega : d ≤ n)
    have hNScaled := mul_le_mul_of_nonneg_left hdn hMin.le
    nlinarith
  have hSum := two_exponential_rates_absorbed (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hLarge
  exact hProbability.trans ((add_le_add hWitness (hNet.trans hNetBound)).trans hSum)

def SourceSteepKernelExclusionLemma : Prop :=
  ∀ cw : ℝ, 0 < cw → cw ≤ 1 / 4 → ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ ≤ 1 / 2 ∧
    ∀ a₃ : ℝ, 0 < a₃ → a₃ ≤ a₀ → ∀ C : ℝ, 0 < C →
      ∀ σ Z₀ : ℝ, 0 < σ → σ < 1 → 0 ≤ Z₀ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ d : ℕ, InLowerBand C σ n d → ∀ L : ℕ, IsKernelCodimension n d L →
          ∀ I : Finset (Fin n), I.card = n - L → ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
            (uniformProbability (fun rows : RowSliceMatrix n d =>
              ∃ v ∈ sourceShiftedT1 n d L, (retainedShiftedMatrix I ζ rows).mulVec v = 0) ≤
                Real.exp (-sourceT1KernelRate cw * n / Real.sqrt d)) ∧
            (uniformProbability (fun rows : RowSliceMatrix n d =>
              ∃ v ∈ sourceShiftedT2 n d L a₃, (retainedShiftedMatrix I ζ rows).mulVec v = 0) ≤
                Real.exp (-sourceT2KernelRate cw * n))

theorem source_steep_kernel_exclusion_lemma : SourceSteepKernelExclusionLemma := by
  intro cw hcw hcwSmall
  let a₀ := min (1 / 4 : ℝ) (equalBlockRateConstant cw / 33600)
  have ha₀ : 0 < a₀ := lt_min (by norm_num) (by positivity [equalBlockRateConstant_pos hcw])
  refine ⟨a₀, ha₀, (min_le_left _ _).trans (by norm_num), ?_⟩
  intro a₃ ha haBound C hC σ Z₀ _ _ hZ
  have haHalf : a₃ ≤ 1 / 2 := haBound.trans ((min_le_left _ _).trans (by norm_num))
  have haRate := haBound.trans (min_le_right (1 / 4 : ℝ) (equalBlockRateConstant cw / 33600))
  have haSmall : 7 * a₃ ≤ equalBlockRateConstant cw / 4800 := by linarith
  have hBoth : ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ I : Finset (Fin n), I.card = n - L →
        ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
          (uniformProbability (fun rows : RowSliceMatrix n d =>
            ∃ v ∈ sourceShiftedT1 n d L, (retainedShiftedMatrix I ζ rows).mulVec v = 0) ≤
              Real.exp (-sourceT1KernelRate cw * n / Real.sqrt d)) ∧
          (uniformProbability (fun rows : RowSliceMatrix n d =>
            ∃ v ∈ sourceShiftedT2 n d L a₃, (retainedShiftedMatrix I ζ rows).mulVec v = 0) ≤
              Real.exp (-sourceT2KernelRate cw * n)) := by
    filter_upwards [eventually_source_shifted_T1_kernel_probability_uniform hC hcw hcwSmall hZ σ,
      eventually_source_shifted_T2_kernel_probability_uniform hC ha haHalf hcw hcwSmall haSmall hZ σ]
      with n hFirst hSecond
    intro d hBand L hL I hI ζ hShift
    exact ⟨hFirst d hBand L hL I hI ζ hShift, hSecond d hBand L hL I hI ζ hShift⟩
  exact eventually_atTop.mp hBoth

end CircularLaw
