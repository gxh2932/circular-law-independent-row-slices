import CircularLaw.RowSliceLightNet
import CircularLaw.NormFiniteNetReduction
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# A polynomial tail for the actual centered real row-slice operator

The light bound on the constructed nets and the simultaneous heavy
bound control every net pair. Mean removal connects the zero-sum
right net to the full right lattice net. The finite-net reduction
then bounds the actual continuous Euclidean operator.
-/

noncomputable section
open Classical
open scoped BigOperators InnerProductSpace

namespace CircularLaw

def normRealMatrixOperator {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 M)

theorem normRealMatrixOperator_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    normRealMatrixOperator M y i = ∑ j, M i j * y j := rfl

theorem normRealMatrixOperator_inner {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, normRealMatrixOperator M y⟫_ℝ = ∑ i, ∑ j, M i j * (x i * y j) := by
  change (∑ i, (∑ j, M i j * y j) * x i) = _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def centeredRectangularSliceMatrixReal {m n d : ℕ} (rows : Fin m → RowSlice n d) :
    Matrix (Fin m) (Fin n) ℝ := fun i j => rectangularSliceMatrixReal rows i j - (d : ℝ) / n

theorem centeredRectangularSliceMatrixReal_rowSum {m n d : ℕ} (hn : 0 < n)
    (rows : Fin m → RowSlice n d) (i : Fin m) :
    ∑ j, centeredRectangularSliceMatrixReal rows i j = 0 := by
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [centeredRectangularSliceMatrixReal, Finset.sum_sub_distrib,
    rectangularSliceMatrixReal_rowSum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem centeredRealOperator_mean_projection {m n d : ℕ} (hn : 0 < n)
    (rows : Fin m → RowSlice n d) (y : EuclideanSpace ℝ (Fin n)) :
    normRealMatrixOperator (centeredRectangularSliceMatrixReal rows) (normMeanProjection y) =
      normRealMatrixOperator (centeredRectangularSliceMatrixReal rows) y := by
  apply WithLp.ofLp_injective
  funext i
  simp only [normRealMatrixOperator_apply, normMeanProjection_apply, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, centeredRectangularSliceMatrixReal_rowSum hn rows,
    zero_mul, sub_zero]

theorem centeredRealOperator_zero_sum_bilinear {m n d : ℕ}
    (rows : Fin m → RowSlice n d) (x : EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin n)) (hSum : ∑ j, y j = 0) :
    ⟪x, normRealMatrixOperator (centeredRectangularSliceMatrixReal rows) y⟫_ℝ =
      weightedSliceMatrixSum (fun i j => x i * y j) rows := by
  rw [normRealMatrixOperator_inner]
  calc
    _ = weightedSliceMatrixSum (fun i j => x i * y j) rows -
        ((d : ℝ) / n) * (∑ i, ∑ j, x i * y j) := by
      rw [weightedSliceMatrixSum_eq_real_bilinear]
      simp only [centeredRectangularSliceMatrixReal, sub_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
    _ = _ := by rw [rankOneWeights_sum_zero _ _ hSum, mul_zero, sub_zero]

theorem weightedSliceMatrixSum_light_heavy {m n d : ℕ} (rows : Fin m → RowSlice n d)
    (Q : Fin m → Fin n → ℝ) (K : ℝ) :
    weightedSliceMatrixSum Q rows = weightedSliceMatrixSum (lightMatrixWeights Q K) rows +
      weightedSliceMatrixSum (heavyMatrixWeights Q K) rows := by
  simp only [weightedSliceMatrixSum_eq_real_bilinear]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_add, matrixWeights_light_add_heavy]

def rowSliceRealNormConstant (B beta : ℝ) : ℝ := 2 * (1 + 3 * B + rowSliceHeavyConstant beta)

theorem rowSliceHeavyConstant_nonneg {beta : ℝ} (hBeta : 0 ≤ beta) :
    0 ≤ rowSliceHeavyConstant beta := by
  unfold rowSliceHeavyConstant normHeavySquareConstant normHeavyBudget
  rw [Real.log_exp]
  positivity

theorem rowSliceRealNormConstant_nonneg {B beta : ℝ} (hB : 0 ≤ B) (hBeta : 0 ≤ beta) :
    0 ≤ rowSliceRealNormConstant B beta := by
  have hHeavy := rowSliceHeavyConstant_nonneg hBeta
  unfold rowSliceRealNormConstant
  positivity

theorem rowSliceLightThreshold_le {d : ℕ} (hd : 0 < d) (B : ℝ) :
    rowSliceLightThreshold d B ≤ (1 + 3 * B) * Real.sqrt d := by
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : Real.sqrt (9 * (d : ℝ)) = 3 * Real.sqrt d := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
    norm_num
  have hSmall : (d : ℝ) / Real.sqrt (9 * (d : ℝ)) ≤ Real.sqrt d := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (by positivity : 0 < 9 * (d : ℝ))), hRoot]
    nlinarith [Real.sq_sqrt hdReal.le]
  unfold rowSliceLightThreshold
  rw [hRoot]
  rw [hRoot] at hSmall
  nlinarith only [hSmall]

theorem rowSlice_real_norm_on_light_heavy {m n d : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hd : 0 < d) {B beta : ℝ}
    (hB : 0 ≤ B) (hBeta : 0 ≤ beta) (rows : Fin m → RowSlice n d)
    (hLight : RowSliceLightNetBound B rows) (hHeavy : RowSliceHeavyBound beta rows) :
    ‖normRealMatrixOperator (centeredRectangularSliceMatrixReal rows)‖ ≤
      rowSliceRealNormConstant B beta * Real.sqrt d := by
  let T := (1 + 3 * B + rowSliceHeavyConstant beta) * Real.sqrt d
  have hT : 0 ≤ T := by
    have hHeavyNonneg := rowSliceHeavyConstant_nonneg hBeta
    positivity
  have hNet : ∀ x ∈ normLatticeNet m, ∀ y ∈ normLatticeNet n,
      |⟪x, normRealMatrixOperator (centeredRectangularSliceMatrixReal rows) y⟫_ℝ| ≤ T := by
    intro x hx y hy
    have hProjected : normMeanProjection y ∈ normZeroMeanNet n :=
      Finset.mem_image.mpr ⟨y, hy, rfl⟩
    have hxNorm := normLatticeNet_norm_bound hm hx
    have hyNorm := normZeroMeanNet_norm_bound hn hProjected
    have hxMass : (∑ i, (x i) ^ 2) ≤ 1 := by
      rw [← real_euclidean_norm_sq]
      nlinarith [norm_nonneg x]
    have hyMass : (∑ j, (normMeanProjection y j) ^ 2) ≤ 1 := by
      rw [← real_euclidean_norm_sq]
      nlinarith [norm_nonneg (normMeanProjection y)]
    rw [← centeredRealOperator_mean_projection hn rows y,
      centeredRealOperator_zero_sum_bilinear rows x _ (normMeanProjection_sum_zero hn y),
      weightedSliceMatrixSum_light_heavy rows _ (Real.sqrt (9 * (d : ℝ)) / n)]
    apply (abs_add_le _ _).trans
    have hPair := add_le_add ((hLight x hx _ hProjected).trans (rowSliceLightThreshold_le hd B))
      (hHeavy (fun i => x i) (fun j => normMeanProjection y j) hxMass hyMass)
    convert hPair using 1
    dsimp [T]
    ring
  have hBound := norm_operator_bound_of_quarter_nets (normLatticeNet m) (normLatticeNet n)
    (normLatticeNet_unit_ball_cover hm) (normLatticeNet_unit_ball_cover hn) hT
    (normRealMatrixOperator (centeredRectangularSliceMatrixReal rows)) hNet
  convert hBound using 1
  unfold rowSliceRealNormConstant T
  ring

theorem rowSlice_real_norm_failure_polynomial {m n d : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) (hmn : m ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    {A : ℝ} (hA : 0 ≤ A) (hDegree : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ)) :
    uniformProbability (fun rows : Fin m → RowSlice n d =>
      rowSliceRealNormConstant (32 * (A + 20)) (A + 2) * Real.sqrt d <
        ‖normRealMatrixOperator (centeredRectangularSliceMatrixReal rows)‖) ≤ (n : ℝ) ^ (-A) := by
  have hnPos : 0 < n := by omega
  have hCover : ∀ rows : Fin m → RowSlice n d,
      rowSliceRealNormConstant (32 * (A + 20)) (A + 2) * Real.sqrt d <
        ‖normRealMatrixOperator (centeredRectangularSliceMatrixReal rows)‖ →
      ¬RowSliceLightNetBound (32 * (A + 20)) rows ∨ ¬RowSliceHeavyBound (A + 2) rows := by
    intro rows hFail
    by_cases hLight : RowSliceLightNetBound (32 * (A + 20)) rows
    · right
      intro hHeavy
      exact (not_lt_of_ge (rowSlice_real_norm_on_light_heavy hm hnPos hd
        (by linarith only [hA]) (by linarith only [hA]) rows hLight hHeavy)) hFail
    · exact Or.inl hLight
  apply (uniformProbability_mono hCover).trans
  apply (uniformProbability_or_le _ _).trans
  have hHeavy : uniformProbability (fun rows : Fin m → RowSlice n d =>
      ¬RowSliceHeavyBound (A + 2) rows) ≤ (n : ℝ) ^ (-(A + 1)) := by
    have hDegree' : (A + 1 + 2) * Real.log (n : ℝ) ≤ 9 * (d : ℝ) := by
      convert hDegree using 1
      ring
    simpa only [add_assoc, one_add_one_eq_two] using
      rowSliceHeavyBound_failure_polynomial hm hn hmn hd hdn
        (by linarith only [hA] : 0 ≤ A + 1) hDegree'
  apply (add_le_add (rowSliceLightNetBound_failure_polynomial hm hn hmn hd hdn hA) hHeavy).trans
  exact inverse_dimension_two_term_budget hn A

end CircularLaw
