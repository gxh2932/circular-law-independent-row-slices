import CircularLaw.IndependentLogTail

/-!
# Lower tails for independent finite coordinate events

Each coordinate has its actual finite uniform law. The Laplace product
gives a bound in terms of the sum of the possibly different probabilities.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem coordinate_lower_laplace_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (E : ∀ i, α i → Prop) (tilt : ℝ) :
    finiteMean (fun x : ∀ i, α i => Real.exp (-tilt * coordinateEventCount E x)) ≤
      Real.exp ((Real.exp (-tilt) - 1) * ∑ i, uniformProbability (E i)) := by
  rw [coordinate_success_laplace E (-tilt)]
  calc
    _ ≤ ∏ i, Real.exp (uniformProbability (E i) * (Real.exp (-tilt) - 1)) := by
      apply Finset.prod_le_prod
      · intro i _
        have hp := uniformProbability_le_one (E i)
        have hProd := mul_nonneg (uniformProbability_nonneg (E i)) (Real.exp_pos (-tilt)).le
        nlinarith
      · intro i _
        have h := Real.add_one_le_exp (uniformProbability (E i) * (Real.exp (-tilt) - 1))
        linarith
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem independent_lower_tail_laplace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (E : ∀ i, α i → Prop) {tilt : ℝ} (htilt : 0 ≤ tilt) (t : ℝ) :
    uniformProbability (fun x : ∀ i, α i => (coordinateEventCount E x : ℝ) < t) ≤
      Real.exp ((Real.exp (-tilt) - 1) * (∑ i, uniformProbability (E i)) + tilt * t) := by
  let f := fun x : ∀ i, α i => Real.exp (-tilt * coordinateEventCount E x)
  let a := Real.exp (-tilt * t)
  have ha : 0 < a := Real.exp_pos _
  have hMark := finite_uniform_markov
    (fun x : ∀ i, α i => (coordinateEventCount E x : ℝ) < t)
    f ha (fun _ => (Real.exp_pos _).le)
    (fun _ hx => Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hx.le (neg_nonpos.mpr htilt)))
  apply hMark.trans
  apply (div_le_div_of_nonneg_right (coordinate_lower_laplace_bound E tilt) ha.le).trans_eq
  dsimp only [a]
  rw [← Real.exp_sub]
  congr 1
  ring

theorem independent_lower_tail_half {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (E : ∀ i, α i → Prop) :
    uniformProbability (fun x : ∀ i, α i =>
      (coordinateEventCount E x : ℝ) < (∑ i, uniformProbability (E i)) / 2) ≤
        Real.exp (-binomialHalfRate * ∑ i, uniformProbability (E i)) := by
  have h := independent_lower_tail_laplace E
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le ((∑ i, uniformProbability (E i)) / 2)
  have hExp : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hExp] at h
  convert h using 1
  unfold binomialHalfRate
  congr 1
  ring

def uniqueWitnessRate : ℝ := 1 / 5 - Real.log (4 / 3) / 2

theorem uniqueWitnessRate_pos : 0 < uniqueWitnessRate := by
  have h := Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num : (4 / 3 : ℝ) ≠ 1)
  unfold uniqueWitnessRate
  linarith

theorem independent_lower_tail_four_fifths {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (E : ∀ i, α i → Prop) (T : ℝ)
    (hMean : (4 / 5 : ℝ) * T ≤ ∑ i, uniformProbability (E i)) :
    uniformProbability (fun x : ∀ i, α i => (coordinateEventCount E x : ℝ) < T / 2) ≤
      Real.exp (-uniqueWitnessRate * T) := by
  have h := independent_lower_tail_laplace E
    (Real.log_pos (by norm_num : (1 : ℝ) < 4 / 3)).le (T / 2)
  have hExp : Real.exp (-Real.log (4 / 3)) = (3 / 4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    norm_num
  rw [hExp] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  unfold uniqueWitnessRate
  linarith

end CircularLaw
