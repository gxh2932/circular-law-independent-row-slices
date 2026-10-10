import CircularLaw.RestrictedNormTheorem
import CircularLaw.CenteredSliceAction

/-!
# The checked norm tail on every deterministic retained set

Restriction decreases the output Euclidean norm. The full centered
operator bound therefore supplies the precise retained norm event used
by canonical net reduction and the structural kernel theorem.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem centeredFullMatrixOperator_action {n d : ℕ} (rows : RowSliceMatrix n d)
    (v : Fin n → ℂ) :
    normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows) (WithLp.toLp 2 v) =
      (WithLp.toLp 2 (fun i => centeredRowLinearForm (rows i) v) : EuclideanSpace ℂ (Fin n)) := by
  apply WithLp.ofLp_injective
  funext i
  simp only [normComplexMatrixOperatorReal_apply, centeredRowLinearForm,
    centeredRectangularSliceMatrixReal_coe]

theorem centeredFullMatrixOperator_retained_bound {n d : ℕ} (I : Finset (Fin n))
    (rows : RowSliceMatrix n d) (B : ℝ)
    (hNorm : ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ ≤
      B * Real.sqrt d) : RetainedCenteredNormBound I rows B := by
  intro v
  apply (euclidean_retained_norm_le I (fun i => centeredRowLinearForm (rows i) v)).trans
  rw [← centeredFullMatrixOperator_action]
  exact (normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)).le_of_opNorm_le
    hNorm (WithLp.toLp 2 v)

theorem retainedCenteredNormBound_failure_polynomial {n d : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) {A : ℝ} (hA : 0 ≤ A)
    (hDegree : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ)) (I : Finset (Fin n)) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬RetainedCenteredNormBound I rows (rowSliceComplexNormConstant A)) ≤ (n : ℝ) ^ (-A) := by
  have hCover : ∀ rows : RowSliceMatrix n d,
      ¬RetainedCenteredNormBound I rows (rowSliceComplexNormConstant A) →
      rowSliceComplexNormConstant A * Real.sqrt d <
        ‖normComplexMatrixOperatorReal (centeredRectangularSliceMatrixReal rows)‖ := by
    intro rows hFail
    by_contra hNorm
    exact hFail (centeredFullMatrixOperator_retained_bound I rows (rowSliceComplexNormConstant A)
      (le_of_not_gt hNorm))
  exact (uniformProbability_mono hCover).trans
    (rowSlice_complex_norm_failure_polynomial (by omega : 0 < n) hn le_rfl hd hdn hA hDegree)

theorem retainedCenteredNormBound_failure_hundred {n d : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (hDegree : 103 * Real.log (n : ℝ) ≤ 9 * (d : ℝ)) (I : Finset (Fin n)) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ¬RetainedCenteredNormBound I rows (rowSliceComplexNormConstant 100)) ≤ 1 / (n : ℝ) ^ 100 := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hTail := retainedCenteredNormBound_failure_polynomial hn hd hdn
    (by norm_num : (0 : ℝ) ≤ 100) (by norm_num; exact hDegree) I
  have hPower : (n : ℝ) ^ (-(100 : ℝ)) = 1 / (n : ℝ) ^ (100 : ℕ) := by
    rw [Real.rpow_neg hnReal.le]
    change ((n : ℝ) ^ ((100 : ℕ) : ℝ))⁻¹ = _
    rw [Real.rpow_natCast, one_div]
  rw [hPower] at hTail
  exact hTail

end CircularLaw
