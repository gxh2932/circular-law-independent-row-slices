import CircularLaw.BernoulliSubsetCountLaplace
import CircularLaw.WeightedMatrixLaplace
import CircularLaw.FiniteProductEventUpperTail

/-!
# Centered signed weights under the actual Bernoulli product law

The coordinate exponential defect bound requires no sign assumption on
the weight. Independence supplies the exact product and the quadratic
moment bound for bounded tilts.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

def bernoulliWeightedCenteredSum {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (w : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∑ i, w i * bernoulliCenteredValue p (x i)

theorem bernoulli_centered_coordinate_exponential_bound (p : ℝ≥0) (hp : p ≤ 1)
    (s : ℝ) :
    (∫ b, Real.exp (s * bernoulliCenteredValue p b) ∂bernoulliCoordinateLaw p hp) ≤
      Real.exp ((p : ℝ) * (Real.exp s - 1 - s)) := by
  have hPoint (b : Bool) : Real.exp (s * bernoulliCenteredValue p b) =
      Real.exp (-s * p) * Real.exp (s * (cond b 1 0 : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    unfold bernoulliCenteredValue
    ring
  simp_rw [hPoint]
  rw [integral_const_mul, bernoulli_coordinate_exponential_integral]
  have hBase : 1 - (p : ℝ) + p * Real.exp s ≤ Real.exp ((p : ℝ) * (Real.exp s - 1)) := by
    linarith [Real.add_one_le_exp ((p : ℝ) * (Real.exp s - 1))]
  apply (mul_le_mul_of_nonneg_left hBase (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

theorem bernoulli_weighted_centered_exponential_product {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : ι → ℝ) (t : ℝ) :
    (∫ x, Real.exp (t * bernoulliWeightedCenteredSum p w x) ∂bernoulliCubeLaw ι p hp) =
      ∏ i, (∫ b, Real.exp ((t * w i) * bernoulliCenteredValue p b) ∂bernoulliCoordinateLaw p hp) := by
  have hPoint (x : ι → Bool) : Real.exp (t * bernoulliWeightedCenteredSum p w x) =
      ∏ i, Real.exp ((t * w i) * bernoulliCenteredValue p (x i)) := by
    rw [bernoulliWeightedCenteredSum, Finset.mul_sum, Real.exp_sum]
    simp only [mul_assoc]
  simp_rw [hPoint]
  rw [bernoulliCubeLaw, integral_fintype_prod_eq_prod
    (fun i b => Real.exp ((t * w i) * bernoulliCenteredValue p b))]

theorem bernoulli_weighted_centered_laplace_defect {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : ι → ℝ) (t : ℝ) :
    (∫ x, Real.exp (t * bernoulliWeightedCenteredSum p w x) ∂bernoulliCubeLaw ι p hp) ≤
      Real.exp ((p : ℝ) * ∑ i, (Real.exp (t * w i) - 1 - t * w i)) := by
  rw [bernoulli_weighted_centered_exponential_product]
  calc
    _ ≤ ∏ i, Real.exp ((p : ℝ) * (Real.exp (t * w i) - 1 - t * w i)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact integral_nonneg (fun _ => Real.exp_nonneg _)
      · intro i _
        exact bernoulli_centered_coordinate_exponential_bound p hp (t * w i)
    _ = _ := by rw [← Real.exp_sum, Finset.mul_sum]

theorem bernoulli_weighted_centered_laplace_quadratic {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : ι → ℝ) {K t : ℝ}
    (hCap : ∀ i, |w i| ≤ K) (hScale : |t| * K ≤ 1) :
    (∫ x, Real.exp (t * bernoulliWeightedCenteredSum p w x) ∂bernoulliCubeLaw ι p hp) ≤
      Real.exp (t ^ 2 * ((p : ℝ) * ∑ i, w i ^ 2)) := by
  apply (bernoulli_weighted_centered_laplace_defect p hp w t).trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (p : ℝ) * ∑ i, (t * w i) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ p.coe_nonneg
      apply Finset.sum_le_sum
      intro i _
      apply real_exp_defect_le_square
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hCap i) (abs_nonneg t)).trans hScale
    _ = _ := by simp_rw [mul_pow, ← Finset.mul_sum]; ring

theorem bernoulli_weighted_centered_upper_tail {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : ι → ℝ) {K t : ℝ}
    (ht : 0 ≤ t) (hCap : ∀ i, |w i| ≤ K) (hScale : |t| * K ≤ 1) (u : ℝ) :
    (bernoulliCubeLaw ι p hp).real {x | u ≤ bernoulliWeightedCenteredSum p w x} ≤
      Real.exp (t ^ 2 * ((p : ℝ) * ∑ i, w i ^ 2) - t * u) := by
  have hMark := finite_measure_event_markov (bernoulliCubeLaw ι p hp)
    (fun x => u ≤ bernoulliWeightedCenteredSum p w x)
    (fun x => Real.exp (t * bernoulliWeightedCenteredSum p w x)) (Real.exp_pos (t * u))
    (fun _ => Real.exp_nonneg _)
    (fun _ hx => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx ht))
  apply hMark.trans
  apply (div_le_div_of_nonneg_right (bernoulli_weighted_centered_laplace_quadratic p hp w hCap hScale)
    (Real.exp_nonneg _)).trans_eq
  exact (Real.exp_sub _ _).symm

theorem bernoulli_weighted_centered_abs_tail {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : ι → ℝ) {K t : ℝ}
    (ht : 0 ≤ t) (hCap : ∀ i, |w i| ≤ K) (hScale : |t| * K ≤ 1) (u : ℝ) :
    (bernoulliCubeLaw ι p hp).real {x | u ≤ |bernoulliWeightedCenteredSum p w x|} ≤
      2 * Real.exp (t ^ 2 * ((p : ℝ) * ∑ i, w i ^ 2) - t * u) := by
  have hNeg (x : ι → Bool) : bernoulliWeightedCenteredSum p (fun i => -w i) x =
      -bernoulliWeightedCenteredSum p w x := by simp [bernoulliWeightedCenteredSum]
  have hCover : {x | u ≤ |bernoulliWeightedCenteredSum p w x|} ⊆
      {x | u ≤ bernoulliWeightedCenteredSum p w x} ∪
      {x | u ≤ bernoulliWeightedCenteredSum p (fun i => -w i) x} := by
    intro x hx
    change u ≤ |bernoulliWeightedCenteredSum p w x| at hx
    change u ≤ bernoulliWeightedCenteredSum p w x ∨
      u ≤ bernoulliWeightedCenteredSum p (fun i => -w i) x
    rw [hNeg]
    exact le_abs.mp hx
  have hPositive := bernoulli_weighted_centered_upper_tail p hp w ht hCap hScale u
  have hNegative := bernoulli_weighted_centered_upper_tail p hp (fun i => -w i) ht
    (by simpa only [abs_neg] using hCap) hScale u
  simp only [neg_sq] at hNegative
  apply (measureReal_mono hCover (h₂ := by finiteness)).trans
  apply (measureReal_union_le _ _).trans
  apply (add_le_add hPositive hNegative).trans_eq
  ring

end CircularLaw
