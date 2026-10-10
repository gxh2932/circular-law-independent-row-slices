import CircularLaw.NormRealComplexTransfer
import CircularLaw.KernelProbabilityAssembly

/-!
# The manuscript restricted operator norm proposition

For every fixed positive exponent a single positive finite constant
controls both the logarithmic degree threshold and the actual centered
complex Euclidean operator. The probability is the independent uniform
row-slice law. No concentration or heavy estimate is an assumed input.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def rowSliceComplexNormConstant (A : ℝ) : ℝ :=
  2 * rowSliceRealNormConstant (32 * (A + 20)) (A + 2)

theorem rowSliceComplexNormConstant_nonneg {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ rowSliceComplexNormConstant A := by
  unfold rowSliceComplexNormConstant
  exact mul_nonneg (by norm_num) (rowSliceRealNormConstant_nonneg (by linarith) (by linarith))

theorem rowSlice_complex_norm_failure_polynomial {m n d : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {A : ℝ} (hA : 0 ≤ A) (hDegree : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ)) :
    uniformProbability (fun rows : Fin m → RowSlice n d =>
      rowSliceComplexNormConstant A * Real.sqrt d <
        ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖) ≤
      (n : ℝ) ^ (-A) := by
  have hConst : 0 ≤ rowSliceRealNormConstant (32 * (A + 20)) (A + 2) :=
    rowSliceRealNormConstant_nonneg (by linarith) (by linarith)
  have hCover : ∀ rows : Fin m → RowSlice n d,
      rowSliceComplexNormConstant A * Real.sqrt d <
        ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ →
      rowSliceRealNormConstant (32 * (A + 20)) (A + 2) * Real.sqrt d <
        ‖normRealMatrixOperator (centeredRectangularSliceMatrixReal rows)‖ := by
    intro rows hFail
    by_contra hReal
    have hBound := normComplexMatrixOperatorReal_norm_bound
      (centeredRectangularSliceMatrixReal rows) (mul_nonneg hConst (Real.sqrt_nonneg _)) (le_of_not_gt hReal)
    unfold rowSliceComplexNormConstant at hFail
    nlinarith only [hFail, hBound]
  exact (uniformProbability_mono hCover).trans
    (rowSlice_real_norm_failure_polynomial hm hn hmn hd hdn hA hDegree)

theorem rowSlice_complex_norm_good_probability {m n d : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {A : ℝ} (hA : 0 ≤ A) (hDegree : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ)) :
    1 - (n : ℝ) ^ (-A) ≤ uniformProbability (fun rows : Fin m → RowSlice n d =>
      ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ≤
        rowSliceComplexNormConstant A * Real.sqrt d) := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  have hFail := rowSlice_complex_norm_failure_polynomial hm hn hmn hd hdn hA hDegree
  have hEvent : (fun rows : Fin m → RowSlice n d =>
      rowSliceComplexNormConstant A * Real.sqrt d <
        ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖) =
      (fun rows : Fin m → RowSlice n d =>
        ¬‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ≤
          rowSliceComplexNormConstant A * Real.sqrt d) := by
    funext rows
    exact propext not_le.symm
  rw [hEvent, uniformProbability_not] at hFail
  linarith only [hFail]

def rowSliceRestrictedNormConstant (A : ℝ) : ℝ :=
  max (A + 3) (rowSliceComplexNormConstant A)

theorem rowSliceRestrictedNormConstant_pos {A : ℝ} (hA : 0 < A) :
    0 < rowSliceRestrictedNormConstant A :=
  lt_of_lt_of_le (by linarith only [hA]) (le_max_left _ _)

/-- The actual centered complex entries are the paper's `H - E H`. -/
theorem rectangularSliceMatrixReal_mean {m n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (i : Fin m) (j : Fin n) :
    finiteMean (fun rows : Fin m → RowSlice n d => rectangularSliceMatrixReal rows i j) =
      (d : ℝ) / n := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  exact (finiteMean_pi_apply i (fun S : RowSlice n d => rowEntryReal S j)).trans
    (row_entry_mean hd hdn j)

/-- The literal real centering agrees with the complex centered row used downstream. -/
theorem centeredRectangularSliceMatrixReal_coe {m n d : ℕ}
    (rows : Fin m → RowSlice n d) (i : Fin m) (j : Fin n) :
    (centeredRectangularSliceMatrixReal rows i j : ℂ) = centeredRow (rows i) j := by
  simp only [centeredRectangularSliceMatrixReal, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_natCast, rectangularSliceMatrixReal, rowEntryReal_coe, centeredRow]

def RestrictedNormTheorem : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ n m d : ℕ, 0 < n → (n : ℝ) / 2 ≤ m → m ≤ n → (d : ℝ) ≤ (n : ℝ) / 2 →
      C * Real.log (n : ℝ) ≤ d →
      1 - (n : ℝ) ^ (-A) ≤ uniformProbability (fun rows : Fin m → RowSlice n d =>
        ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ≤ C * Real.sqrt d)

theorem restricted_norm_theorem : RestrictedNormTheorem := by
  intro A hA
  refine ⟨rowSliceRestrictedNormConstant A, rowSliceRestrictedNormConstant_pos hA, ?_⟩
  intro n m d hn hLower hUpper hDegreeUpper hDegree
  by_cases hnTwo : 2 ≤ n
  · have hnReal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hm : 0 < m := by
      have hPositive : (0 : ℝ) < m := by linarith only [hLower, hnReal]
      exact_mod_cast hPositive
    have hdn : d ≤ n := by
      have hdnReal : (d : ℝ) ≤ n := by linarith only [hDegreeUpper, hnReal]
      exact_mod_cast hdnReal
    have hLog : 0 < Real.log (n : ℝ) := Real.log_pos hnReal
    have hCPos := rowSliceRestrictedNormConstant_pos hA
    have hd : 0 < d := by
      have hPositive : (0 : ℝ) < d := lt_of_lt_of_le (mul_pos hCPos hLog) hDegree
      exact_mod_cast hPositive
    have hNeeded : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ) := by
      have hSmall := (mul_le_mul_of_nonneg_right
        (le_max_left (A + 3) (rowSliceComplexNormConstant A)) hLog.le).trans hDegree
      nlinarith only [hSmall, show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
    apply (rowSlice_complex_norm_good_probability hm hnTwo hUpper hd hdn hA.le hNeeded).trans
    apply uniformProbability_mono
    intro rows hGood
    exact hGood.trans (mul_le_mul_of_nonneg_right
      (le_max_right (A + 3) (rowSliceComplexNormConstant A)) (Real.sqrt_nonneg _))
  · have hnOne : n = 1 := by omega
    subst n
    simpa only [Nat.cast_one, Real.one_rpow, sub_self] using
      uniformProbability_nonneg (fun rows : Fin m → RowSlice 1 d =>
        ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ≤
          rowSliceRestrictedNormConstant A * Real.sqrt d)

end CircularLaw
