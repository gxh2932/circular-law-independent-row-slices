import CircularLaw.SpectralRescalingBound
import CircularLaw.MatrixEnergyShift
import CircularLaw.Conditioning

/-!
# The actual row-slice ESD at the two manuscript normalizations

The `sqrt(d)` normalization has deterministic energy per dimension one.
Schur's bound makes the full bounded-Lipschitz rescaling error at most
`abs((1-d/n)^(-1/2)-1)`. This error tends to zero for every sparse degree
sequence and transfers circular convergence to the variance normalization.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace CircularLaw

def degreeNormalizedMatrix {n d : ℕ} (s : RowSliceMatrix n d) : Matrix (Fin n) (Fin n) ℂ :=
  (Real.sqrt (d : ℝ) : ℂ)⁻¹ • sliceMatrix s

def bulkRescalingFactor (n d : ℕ) : ℝ := (Real.sqrt (1 - (d : ℝ) / n))⁻¹

theorem variance_normalized_matrix_eq_rescaled {n d : ℕ} (s : RowSliceMatrix n d) :
    normalizedMatrix s = (bulkRescalingFactor n d : ℂ) • degreeNormalizedMatrix s := by
  simp only [normalizedMatrix, degreeNormalizedMatrix, bulkRescalingFactor, bulkScaleSq,
    Real.sqrt_mul (Nat.cast_nonneg d), Complex.ofReal_mul, Complex.ofReal_inv,
    mul_inv_rev, smul_smul]

theorem degree_normalized_matrix_energy {n d : ℕ} (s : RowSliceMatrix n d) (hd : 0 < d) :
    squareMatrixEnergy (degreeNormalizedMatrix s) = n := by
  rw [degreeNormalizedMatrix, squareMatrixEnergy_sqrt_normalization,
    show squareMatrixEnergy (sliceMatrix s) = (n : ℝ) * d from frobenius_sq s]
  exact mul_div_cancel_right₀ _ (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)

theorem variance_normalization_esd_distance_bound {n d : ℕ}
    (s : RowSliceMatrix n d) (hd : 0 < d) (hdn : d < n) :
    boundedLipschitzDistance (empiricalSpectralMeasure (normalizedMatrix s))
      (empiricalSpectralMeasure (degreeNormalizedMatrix s)) ≤
      ENNReal.ofReal |bulkRescalingFactor n d - 1| := by
  rw [variance_normalized_matrix_eq_rescaled]
  have h := empirical_spectral_rescaling_distance_bound (degreeNormalizedMatrix s)
    (bulkRescalingFactor n d : ℂ)
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (lt_trans hd hdn).ne'
  have hNorm : ‖(bulkRescalingFactor n d : ℂ) - 1‖ = |bulkRescalingFactor n d - 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  simpa only [degree_normalized_matrix_energy s hd, div_self hn, Real.sqrt_one, mul_one, hNorm]
    using h

theorem bulkRescalingFactor_tendsto (d : ℕ → ℕ) (hsparse : SparseDegrees d) :
    Tendsto (fun n => bulkRescalingFactor n (d n)) atTop (𝓝 1) := by
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hRoot : Tendsto (fun n => Real.sqrt (1 - (d n : ℝ) / n)) atTop (𝓝 1) := by
    simpa only [sub_zero, Real.sqrt_one] using (hOne.sub hsparse).sqrt
  simpa only [bulkRescalingFactor, inv_one] using hRoot.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

theorem variance_normalization_error_tendsto (d : ℕ → ℕ) (hsparse : SparseDegrees d) :
    Tendsto (fun n => |bulkRescalingFactor n (d n) - 1|) atTop (𝓝 0) := by
  simpa only [sub_self, abs_zero] using ((bulkRescalingFactor_tendsto d hsparse).sub_const 1).abs

def degreeCircularTail (d : ℕ → ℕ) (epsilon : ℝ) (n : ℕ) : ℝ :=
  uniformProbability fun s : RowSliceMatrix n (d n) => ENNReal.ofReal epsilon <
    boundedLipschitzDistance (empiricalSpectralMeasure (degreeNormalizedMatrix s)) circularMeasure

def DegreeCircularConvergence (d : ℕ → ℕ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → Tendsto (degreeCircularTail d epsilon) atTop (𝓝 0)

theorem variance_normalizations_uniformly_close (d : ℕ → ℕ)
    (hValid : ∀ᶠ n in atTop, 0 < d n ∧ d n < n) (hsparse : SparseDegrees d)
    {epsilon : ℝ} (hEpsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ s : RowSliceMatrix n (d n),
      boundedLipschitzDistance (empiricalSpectralMeasure (normalizedMatrix s))
        (empiricalSpectralMeasure (degreeNormalizedMatrix s)) ≤ ENNReal.ofReal epsilon := by
  filter_upwards [hValid, (variance_normalization_error_tendsto d hsparse).eventually
    (gt_mem_nhds hEpsilon)] with n hn he
  intro s
  exact (variance_normalization_esd_distance_bound s hn.1 hn.2).trans
    (ENNReal.ofReal_le_ofReal he.le)

theorem variance_normalized_circular_tail_transfer (d : ℕ → ℕ) (l : Filter ℕ)
    (hValid : ∀ᶠ n in l, 0 < d n ∧ d n < n)
    (hError : Tendsto (fun n => |bulkRescalingFactor n (d n) - 1|) l (𝓝 0))
    (hDegree : ∀ epsilon : ℝ, 0 < epsilon → Tendsto (degreeCircularTail d epsilon) l (𝓝 0)) :
    ∀ epsilon : ℝ, 0 < epsilon → Tendsto (circularTail d epsilon) l (𝓝 0) := by
  intro epsilon hEpsilon
  have hHalf : 0 < epsilon / 2 := by linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hDegree (epsilon / 2) hHalf)
    (Eventually.of_forall (fun _ => uniformProbability_nonneg _))
  filter_upwards [hValid, hError.eventually (gt_mem_nhds hHalf)] with n hn he
  apply uniformProbability_mono
  intro s hs
  change ENNReal.ofReal (epsilon / 2) <
    boundedLipschitzDistance (empiricalSpectralMeasure (degreeNormalizedMatrix s)) circularMeasure
  by_contra h
  have hDistance := (boundedLipschitzDistance_triangle
    (empiricalSpectralMeasure (normalizedMatrix s))
    (empiricalSpectralMeasure (degreeNormalizedMatrix s)) circularMeasure).trans
      (add_le_add (variance_normalization_esd_distance_bound s hn.1 hn.2) (le_of_not_gt h))
  have hError : ENNReal.ofReal |bulkRescalingFactor n (d n) - 1| +
      ENNReal.ofReal (epsilon / 2) ≤ ENNReal.ofReal epsilon := by
    rw [← ENNReal.ofReal_add (abs_nonneg _) hHalf.le]
    apply ENNReal.ofReal_le_ofReal
    linarith
  exact (not_lt.mpr (hDistance.trans hError)) hs

theorem variance_normalized_circular_convergence_of_degree (d : ℕ → ℕ)
    (hValid : ∀ᶠ n in atTop, 0 < d n ∧ d n < n) (hsparse : SparseDegrees d)
    (hDegree : DegreeCircularConvergence d) : CircularConvergence d :=
  variance_normalized_circular_tail_transfer d atTop hValid
    (variance_normalization_error_tendsto d hsparse) hDegree

theorem variance_normalized_circular_convergence_of_log_lower_bound {C : ℝ} {d : ℕ → ℕ}
    (hC : 0 < C) (hLog : LogLowerBound C d) (hsparse : SparseDegrees d)
    (hDegree : DegreeCircularConvergence d) : CircularConvergence d :=
  variance_normalized_circular_convergence_of_degree d
    (eventually_valid_degrees hC hLog hsparse) hsparse hDegree

theorem convergence_of_degree_regime_tail_bounds (d : ℕ → ℕ)
    (hValid : ∀ᶠ n in atTop, 0 < d n ∧ d n < n) (hsparse : SparseDegrees d)
    (hLow : ∀ epsilon : ℝ, 0 < epsilon → Tendsto (degreeCircularTail d epsilon)
      (atTop ⊓ 𝓟 (lowerRegime d)) (𝓝 0))
    (hHigh : ∀ epsilon : ℝ, 0 < epsilon → Tendsto (degreeCircularTail d epsilon)
      (atTop ⊓ 𝓟 (lowerRegime d)ᶜ) (𝓝 0)) : CircularConvergence d := by
  have hError := variance_normalization_error_tendsto d hsparse
  exact convergence_of_regime_tail_bounds d
    (variance_normalized_circular_tail_transfer d _ (hValid.filter_mono inf_le_left)
      (hError.mono_left inf_le_left) hLow)
    (variance_normalized_circular_tail_transfer d _ (hValid.filter_mono inf_le_left)
      (hError.mono_left inf_le_left) hHigh)

end CircularLaw
