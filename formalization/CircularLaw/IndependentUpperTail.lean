import CircularLaw.IndependentLowerTail

/-!
# Upper tails for the actual finite independent events

The checked product Laplace transform supplies the upper tail. With
each event probability at most `1/16`, more than one eighth of the
coordinates occur with probability at most `exp(-rowLoadRate*K)`.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem independent_upper_tail_laplace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (E : ∀ i, α i → Prop) {tilt : ℝ} (htilt : 0 ≤ tilt) (t : ℝ) :
    uniformProbability (fun x : ∀ i, α i => t < (coordinateEventCount E x : ℝ)) ≤
      Real.exp ((Real.exp tilt - 1) * (∑ i, uniformProbability (E i)) - tilt * t) := by
  let f := fun x : ∀ i, α i => Real.exp (tilt * coordinateEventCount E x)
  let a := Real.exp (tilt * t)
  have ha : 0 < a := Real.exp_pos _
  have hMark := finite_uniform_markov (fun x : ∀ i, α i => t < (coordinateEventCount E x : ℝ))
    f ha (fun _ => (Real.exp_pos _).le)
    (fun _ hx => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.le htilt))
  have hMean : finiteMean f ≤ Real.exp ((Real.exp tilt - 1) * ∑ i, uniformProbability (E i)) := by
    simpa only [neg_neg] using coordinate_lower_laplace_bound E (-tilt)
  apply hMark.trans
  apply (div_le_div_of_nonneg_right hMean ha.le).trans_eq
  dsimp only [a]
  rw [← Real.exp_sub]

def rowLoadRate : ℝ := Real.log 2 / 8 - 1 / 16

theorem rowLoadRate_pos : 0 < rowLoadRate := by
  have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  rw [Real.log_inv] at h
  norm_num at h
  unfold rowLoadRate
  linarith

theorem independent_many_events_sixteenth {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (E : ∀ i, α i → Prop) (hSmall : ∀ i, uniformProbability (E i) ≤ 1 / 16) :
    uniformProbability (fun x : ∀ i, α i =>
      (Fintype.card ι : ℝ) / 8 < coordinateEventCount E x) ≤
        Real.exp (-rowLoadRate * Fintype.card ι) := by
  have h := independent_upper_tail_laplace E
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le ((Fintype.card ι : ℝ) / 8)
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  have hSum : (∑ i, uniformProbability (E i)) ≤ (Fintype.card ι : ℝ) / 16 := by
    have hBound := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hSmall i)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv, mul_one, one_mul] using hBound
  apply h.trans
  apply Real.exp_le_exp.mpr
  unfold rowLoadRate
  linarith

end CircularLaw
