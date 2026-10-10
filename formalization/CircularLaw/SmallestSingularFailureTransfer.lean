import CircularLaw.RowSliceConditionalCircularRegimes

/-!
# Exact smallest-singular-value events supplying the regime deductions

The source's event uses a non-strict smallest-singular-value threshold.
It dominates the joint failure event used for removal of regularization.
Its `C1/sqrt(d)` bound tends to zero. Bounded source exponents supply the
literal lower-band cutoff, while every fixed spectral shift eventually
satisfies the imported shift restriction. The source probability bound
itself is an explicit hypothesis throughout.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

def squareSmallestSingularFailure {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℝ) : Prop :=
  ∃ j, orderedSquareSingularValues A j ≤ τ

def smallestSingularFailureSum (n d : ℕ) (ζ : ℂ) (τA τB : ℝ) : ℝ :=
  (rowSliceMatrixLaw n d).real {rows | squareSmallestSingularFailure (fullShiftedSliceMatrix ζ rows) τA} +
    (sparseBernoulliMatrixLaw n d).real
      {x | squareSmallestSingularFailure (bernoulliSquareMatrix x - ζ • 1) τB}

theorem square_smallest_singular_failure_iff_last {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℝ) :
    squareSmallestSingularFailure A τ ↔
      orderedSquareSingularValues A ⟨n - 1, by omega⟩ ≤ τ := by
  constructor
  · rintro ⟨j, hj⟩
    have hLast : j ≤ (⟨n - 1, by omega⟩ : Fin n) := by
      change j.val ≤ n - 1
      exact Nat.le_pred_of_lt j.isLt
    exact (orderedSquareSingularValues_antitone A hLast).trans hj
  · intro h
    exact ⟨⟨n - 1, by omega⟩, h⟩

theorem smallest_singular_failure_sum_nonneg (n d : ℕ) (ζ : ℂ) (τA τB : ℝ) :
    0 ≤ smallestSingularFailureSum n d ζ τA τB :=
  add_nonneg measureReal_nonneg measureReal_nonneg

theorem independent_square_minimum_failure_le_smallest_sum {n d : ℕ} (hdn : d ≤ n)
    (ζ : ℂ) (τ τA τB : ℝ) (hτA : τ ≤ τA) (hτB : τ ≤ τB) :
    (independentSquareComparisonLaw n d).real (independentSquareMinimumFailure n d ζ τ) ≤
      smallestSingularFailureSum n d ζ τA τB := by
  haveI := rowSliceMatrixLaw_probability hdn
  apply (independent_square_minimum_failure_probability_le hdn ζ τ).trans
  apply add_le_add
  · apply measureReal_mono (h₂ := by finiteness)
    intro rows hRows
    obtain ⟨j, hj⟩ := not_forall.mp hRows
    exact ⟨j, (lt_of_not_ge hj).le.trans hτA⟩
  · apply measureReal_mono (h₂ := by finiteness)
    intro x hx
    obtain ⟨j, hj⟩ := not_forall.mp hx
    exact ⟨j, (lt_of_not_ge hj).le.trans hτB⟩

theorem inverse_sqrt_degree_error_tendsto_zero (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (C1 : ℝ) :
    Tendsto (fun n => C1 / Real.sqrt (d n : ℝ)) atTop (𝓝 0) := by
  have hD : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDegree
  have hRoot := Real.tendsto_sqrt_atTop.comp hD
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds (x := C1)).mul hRoot.inv_tendsto_atTop

theorem independent_square_minimum_failure_of_smallest_sum_bound (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    (ζ : ℕ → ℂ) (τ τA τB : ℕ → ℝ) (C1 : ℝ)
    (hThreshold : ∀ᶠ n in atTop, τ n ≤ τA n ∧ τ n ≤ τB n)
    (hBound : ∀ᶠ n in atTop, smallestSingularFailureSum n (d n) (ζ n) (τA n) (τB n) ≤
      C1 / Real.sqrt (d n : ℝ)) :
    Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      (independentSquareMinimumFailure n (d n) (ζ n) (τ n))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (inverse_sqrt_degree_error_tendsto_zero d hDegree C1)
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse, hThreshold, hBound]
    with n hd hτn hBn
  exact (independent_square_minimum_failure_le_smallest_sum hd.2 (ζ n) (τ n) (τA n) (τB n)
    hτn.1 hτn.2).trans hBn

theorem eventually_fixed_shift_in_smallest_range (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (z : ℂ) :
    ∀ᶠ n in atTop, ‖z * (Real.sqrt (d n : ℝ) : ℂ)‖ ≤
      Real.sqrt (d n : ℝ) * Real.log (Real.log (d n : ℝ)) := by
  have hD : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hDegree
  have hLogLog := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hD)
  filter_upwards [hLogLog.eventually_ge_atTop ‖z‖] with n hn
  rw [shifted_sqrt_degree_norm]
  calc
    _ ≤ Real.log (Real.log (d n : ℝ)) * Real.sqrt (d n : ℝ) :=
      mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg (d n : ℝ))
    _ = _ := mul_comm _ _

theorem lower_cutoff_le_exponent_threshold {n : ℕ} (hn : 1 ≤ n) {CL β : ℝ}
    (hβ : β ≤ CL * Real.log (Real.log n)) :
    lowerHermitizationCutoff n CL ≤ Real.rpow (n : ℝ) (-β) := by
  unfold lowerHermitizationCutoff
  simpa only [Real.rpow_eq_pow] using
    Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ n by exact_mod_cast hn) (neg_le_neg hβ)

theorem lower_minimum_failure_of_exponent_bounds (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    (z : ℂ) (CL C1 : ℝ) (β βB : ℕ → ℝ)
    (hExponents : ∀ᶠ n : ℕ in atTop, β n ≤ CL * Real.log (Real.log n) ∧
      βB n ≤ CL * Real.log (Real.log n))
    (hBound : ∀ᶠ n : ℕ in atTop,
      smallestSingularFailureSum n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ))
        (Real.rpow (n : ℝ) (-β n)) (Real.rpow (n : ℝ) (-βB n)) ≤ C1 / Real.sqrt (d n : ℝ)) :
    Tendsto (fun n => (independentSquareComparisonLaw n (d n)).real
      (independentSquareMinimumFailure n (d n) (z * (Real.sqrt (d n : ℝ) : ℂ))
        (lowerHermitizationCutoff n CL))) atTop (𝓝 0) := by
  apply independent_square_minimum_failure_of_smallest_sum_bound d hDegree hSparse
    (fun n => z * (Real.sqrt (d n : ℝ) : ℂ)) (fun n => lowerHermitizationCutoff n CL)
    (fun n => Real.rpow (n : ℝ) (-β n)) (fun n => Real.rpow (n : ℝ) (-βB n)) C1 _ hBound
  filter_upwards [hExponents, eventually_ge_atTop 1] with n hβn hn
  exact ⟨lower_cutoff_le_exponent_threshold hn hβn.1, lower_cutoff_le_exponent_threshold hn hβn.2⟩

end CircularLaw
