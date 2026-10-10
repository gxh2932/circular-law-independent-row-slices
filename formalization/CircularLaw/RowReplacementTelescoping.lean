import CircularLaw.RowHybridExpectation

/-!
# Telescoping expected absolute hybrid increments

No independence between increments is used. Their individual expectation
bounds and the triangle inequality give the endpoint bound. Since `k<n`,
normalization by `n` leaves the same one-row rate.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem finite_expected_telescope {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsFiniteMeasure ν] (f : ℕ → α → ℝ) (k : ℕ) (B : ℝ)
    (hStep : ∀ i < k, (∫ x, |f (i + 1) x - f i x| ∂ν) ≤ B) :
    (∫ x, |f k x - f 0 x| ∂ν) ≤ (k : ℝ) * B := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hPrev := ih (fun i hi => hStep i (Nat.lt_succ_of_lt hi))
    calc
      _ ≤ ∫ x, |f (k + 1) x - f k x| + |f k x - f 0 x| ∂ν :=
        integral_mono Integrable.of_finite Integrable.of_finite
          (fun x => abs_sub_le (f (k + 1) x) (f k x) (f 0 x))
      _ = (∫ x, |f (k + 1) x - f k x| ∂ν) + (∫ x, |f k x - f 0 x| ∂ν) :=
        integral_add Integrable.of_finite Integrable.of_finite
      _ ≤ B + (k : ℝ) * B := add_le_add (hStep k (Nat.lt_succ_self k)) hPrev
      _ = ((k + 1 : ℕ) : ℝ) * B := by push_cast; ring

theorem row_replacement_finite_product_succ {m n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (hkn : m + 1 < n) {η : ℝ} (hη : 0 < η)
    (u : Fin (m + 1) → EuclideanSpace ℂ (Fin n))
    (hQ : 1 ≤ rowLogComparisonQ n d (n - (m + 1))) :
    (1 / (n : ℝ)) *
      (∫ rows, |regularizedRowPotential (rowHybridMatrix u (m + 1) rows) η -
        regularizedRowPotential (rowHybridMatrix u 0 rows) η|
        ∂Measure.pi (fun _ : Fin (m + 1) => replacementRowPairLaw (by omega) hdn)) ≤
      rowReplacementErrorBound n d (m + 1) η (rowShiftNormBound u) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hTel := finite_expected_telescope
    (Measure.pi (fun _ : Fin (m + 1) => replacementRowPairLaw (by omega) hdn))
    (fun t rows => regularizedRowPotential (rowHybridMatrix u t rows) η) (m + 1)
    (rowReplacementErrorBound n d (m + 1) η (rowShiftNormBound u))
    (fun i hi => rowHybrid_expected_increment_le hd hdn hkn hη u hQ ⟨i, hi⟩)
  have hB := rowReplacementErrorBound_nonneg n d (m + 1) hη (rowShiftNormBound u)
  have hRatio : ((m + 1 : ℕ) : ℝ) / n ≤ 1 :=
    (div_le_one hn).mpr (by exact_mod_cast hkn.le)
  calc
    _ ≤ (1 / (n : ℝ)) * (((m + 1 : ℕ) : ℝ) *
        rowReplacementErrorBound n d (m + 1) η (rowShiftNormBound u)) :=
      mul_le_mul_of_nonneg_left hTel (by positivity)
    _ = (((m + 1 : ℕ) : ℝ) / n) *
        rowReplacementErrorBound n d (m + 1) η (rowShiftNormBound u) := by ring
    _ ≤ 1 * rowReplacementErrorBound n d (m + 1) η (rowShiftNormBound u) :=
      mul_le_mul_of_nonneg_right hRatio hB
    _ = _ := one_mul _

theorem row_replacement_finite_product {n d k : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (hk : 1 ≤ k) (hkn : k < n) {η : ℝ} (hη : 0 < η)
    (u : Fin k → EuclideanSpace ℂ (Fin n))
    (hQ : 1 ≤ rowLogComparisonQ n d (n - k)) :
    (1 / (n : ℝ)) *
      (∫ rows, |regularizedRowPotential (rowHybridMatrix u k rows) η -
        regularizedRowPotential (rowHybridMatrix u 0 rows) η|
        ∂Measure.pi (fun _ : Fin k => replacementRowPairLaw (by omega) hdn)) ≤
      rowReplacementErrorBound n d k η (rowShiftNormBound u) := by
  cases k with
  | zero => omega
  | succ m => exact row_replacement_finite_product_succ hd hdn hkn hη u hQ

end CircularLaw
