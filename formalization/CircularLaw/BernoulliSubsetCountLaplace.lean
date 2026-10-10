import CircularLaw.BernoulliCubeLaw
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Actual Bernoulli subset counts and exponential tails

The exponential moment factors under the actual coordinate product law.
This supplies a tail estimate for every fixed entry set, including empty
sets and Bernoulli parameters zero and one.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

def bernoulliSubsetCount {ι : Type*} (S : Finset ι) (x : ι → Bool) : ℝ :=
  ∑ i ∈ S, (cond (x i) 1 0 : ℝ)

theorem bernoulli_subset_count_nonneg {ι : Type*} (S : Finset ι) (x : ι → Bool) :
    0 ≤ bernoulliSubsetCount S x := by
  apply Finset.sum_nonneg
  intro i _
  cases x i <;> norm_num

theorem bernoulli_coordinate_exponential_integral (p : ℝ≥0) (hp : p ≤ 1) (t : ℝ) :
    (∫ b, Real.exp (t * (cond b 1 0 : ℝ)) ∂bernoulliCoordinateLaw p hp) =
      1 - (p : ℝ) + p * Real.exp t := by
  rw [bernoulliCoordinateLaw_integral]
  simp only [Bool.cond_false, Bool.cond_true, mul_zero, mul_one, Real.exp_zero, mul_one]

theorem bernoulli_subset_count_exponential_eq_prod {ι : Type*} [Fintype ι]
    (S : Finset ι) (t : ℝ) (x : ι → Bool) :
    Real.exp (t * bernoulliSubsetCount S x) =
      ∏ i, (if i ∈ S then Real.exp (t * (cond (x i) 1 0 : ℝ)) else 1) := by
  rw [Fintype.prod_ite_mem, bernoulliSubsetCount, Finset.mul_sum, Real.exp_sum]

theorem bernoulli_subset_count_exponential_integral {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) (t : ℝ) :
    (∫ x, Real.exp (t * bernoulliSubsetCount S x) ∂bernoulliCubeLaw ι p hp) =
      (1 - (p : ℝ) + p * Real.exp t) ^ S.card := by
  simp_rw [bernoulli_subset_count_exponential_eq_prod]
  rw [bernoulliCubeLaw, integral_fintype_prod_eq_prod
    (fun i b => if i ∈ S then Real.exp (t * (cond b 1 0 : ℝ)) else 1)]
  have hCoordinate (i : ι) :
      (∫ b, (if i ∈ S then Real.exp (t * (cond b 1 0 : ℝ)) else 1) ∂bernoulliCoordinateLaw p hp) =
        if i ∈ S then 1 - (p : ℝ) + p * Real.exp t else 1 := by
    by_cases hi : i ∈ S
    · simp only [if_pos hi, bernoulli_coordinate_exponential_integral]
    · simp only [if_neg hi, integral_const, probReal_univ, one_smul]
  simp_rw [hCoordinate]
  rw [Fintype.prod_ite_mem, Finset.prod_const]

theorem bernoulli_subset_count_exponential_integral_le {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) (t : ℝ) :
    (∫ x, Real.exp (t * bernoulliSubsetCount S x) ∂bernoulliCubeLaw ι p hp) ≤
      Real.exp ((S.card : ℝ) * p * (Real.exp t - 1)) := by
  rw [bernoulli_subset_count_exponential_integral]
  have hpReal : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hBase : 0 ≤ 1 - (p : ℝ) + p * Real.exp t :=
    add_nonneg (sub_nonneg.mpr hpReal) (mul_nonneg p.coe_nonneg (Real.exp_pos t).le)
  have hCompare : 1 - (p : ℝ) + p * Real.exp t ≤ Real.exp ((p : ℝ) * (Real.exp t - 1)) := by
    have h := Real.add_one_le_exp ((p : ℝ) * (Real.exp t - 1))
    linarith
  apply (pow_le_pow_left₀ hBase hCompare S.card).trans_eq
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem bernoulli_subset_count_upper_tail {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    (bernoulliCubeLaw ι p hp).real {x | u ≤ bernoulliSubsetCount S x} ≤
      Real.exp ((S.card : ℝ) * p * (Real.exp t - 1) - t * u) := by
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (bernoulliCubeLaw ι p hp) (fun x =>
      (Real.exp_pos (t * bernoulliSubsetCount S x)).le))
    (Integrable.of_finite : Integrable (fun x => Real.exp (t * bernoulliSubsetCount S x))
      (bernoulliCubeLaw ι p hp)) (Real.exp (t * u))
  have hSubset : {x | u ≤ bernoulliSubsetCount S x} ⊆
      {x | Real.exp (t * u) ≤ Real.exp (t * bernoulliSubsetCount S x)} := by
    intro x hx
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx ht)
  have hEvent := measureReal_mono (μ := bernoulliCubeLaw ι p hp) hSubset
  have hMul := (mul_le_mul_of_nonneg_left hEvent (Real.exp_pos (t * u)).le).trans hMark
  have hBound := hMul.trans (bernoulli_subset_count_exponential_integral_le p hp S t)
  calc
    _ ≤ Real.exp ((S.card : ℝ) * p * (Real.exp t - 1)) / Real.exp (t * u) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hBound)
    _ = _ := (Real.exp_sub _ _).symm

end CircularLaw
