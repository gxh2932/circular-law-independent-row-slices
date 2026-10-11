import CircularLaw.BernoulliOperatorNorm
import CircularLaw.BernoulliMatrixWordMeans
import CircularLaw.CenteredSliceAction

/-!
# The actual centered Bernoulli norm after every deterministic row deletion

The full operator controls all retained sets simultaneously, so deleting
a row introduces no additional probability union cost.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def retainedCenteredBernoulliMatrix {n : ℕ} (I : Finset (Fin n)) (d : ℕ)
    (sample : BernoulliSquareSample n) : Matrix I (Fin n) ℂ :=
  (bernoulliCenteredSquareMatrix (rowBernoulliParameter n d) sample).submatrix Subtype.val id

def BernoulliRetainedCenteredNormBound {n : ℕ} (I : Finset (Fin n)) (d : ℕ)
    (sample : BernoulliSquareSample n) (B : ℝ) : Prop :=
  ∀ x : EuclideanSpace ℂ (Fin n),
    ‖(retainedCenteredBernoulliMatrix I d sample).toEuclideanLin x‖ ≤
      B * Real.sqrt d * ‖x‖

theorem centered_bernoulli_matrix_real_coe {n : ℕ} (d : ℕ) (sample : BernoulliSquareSample n)
    (i j : Fin n) :
    (centeredBernoulliMatrixReal d sample i j : ℂ) =
      bernoulliCenteredSquareMatrix (rowBernoulliParameter n d) sample i j := by
  simp only [centeredBernoulliMatrixReal, bernoulliSquareMatrixReal,
    bernoulliCenteredSquareMatrix, bernoulliCenteredValue, rowBernoulliParameter_coe]

theorem bernoulli_centered_full_operator_action {n : ℕ} (d : ℕ)
    (sample : BernoulliSquareSample n) (x : EuclideanSpace ℂ (Fin n)) :
    normComplexMatrixOperatorReal (centeredBernoulliMatrixReal d sample) x =
      (bernoulliCenteredSquareMatrix (rowBernoulliParameter n d) sample).toEuclideanLin x := by
  apply WithLp.ofLp_injective
  funext i
  simp only [normComplexMatrixOperatorReal_apply, centered_bernoulli_matrix_real_coe]
  rfl

theorem bernoulli_centered_full_operator_retained_bound {n : ℕ} (I : Finset (Fin n))
    (d : ℕ) (sample : BernoulliSquareSample n) (B : ℝ)
    (hNorm : ‖normComplexMatrixOperatorReal (centeredBernoulliMatrixReal d sample)‖ ≤ B * Real.sqrt d) :
    BernoulliRetainedCenteredNormBound I d sample B := by
  intro x
  have hFull := bernoulli_centered_full_operator_action d sample x
  have hRestriction : (retainedCenteredBernoulliMatrix I d sample).toEuclideanLin x =
      (WithLp.toLp 2 (fun i : I =>
        (bernoulliCenteredSquareMatrix (rowBernoulliParameter n d) sample).toEuclideanLin x i.val) :
        EuclideanSpace ℂ I) := by
    rfl
  rw [hRestriction]
  apply (euclidean_retained_norm_le I (fun i =>
    (bernoulliCenteredSquareMatrix (rowBernoulliParameter n d) sample).toEuclideanLin x i)).trans
  change ‖(bernoulliCenteredSquareMatrix (rowBernoulliParameter n d) sample).toEuclideanLin x‖ ≤ _
  rw [← hFull]
  exact (normComplexMatrixOperatorReal (centeredBernoulliMatrixReal d sample)).le_of_opNorm_le hNorm x

theorem bernoulli_retained_centered_norm_simultaneous_failure {n d : ℕ}
    (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n) {A : ℝ} (hA : 0 ≤ A)
    (hDegree : (A + 3) * Real.log (n : ℝ) ≤ 9 * (d : ℝ)) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ¬∀ I : Finset (Fin n), BernoulliRetainedCenteredNormBound I d sample (bernoulliComplexNormConstant A)} ≤
        (n : ℝ) ^ (-A) := by
  have hCover : {sample : BernoulliSquareSample n |
      ¬∀ I : Finset (Fin n), BernoulliRetainedCenteredNormBound I d sample (bernoulliComplexNormConstant A)} ⊆
      {sample | bernoulliComplexNormConstant A * Real.sqrt d <
        ‖normComplexMatrixOperatorReal (centeredBernoulliMatrixReal d sample)‖} := by
    intro sample hFail
    by_contra hNot
    exact hFail (fun I => bernoulli_centered_full_operator_retained_bound I d sample
      (bernoulliComplexNormConstant A) (le_of_not_gt hNot))
  exact (measureReal_mono hCover (h₂ := by finiteness)).trans
    (bernoulli_complex_norm_failure_polynomial hn hd hdn hA hDegree)

end CircularLaw
