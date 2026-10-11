import CircularLaw.CubeSum

/-!
# The removal step in Miroshnikov's concentration estimate

Choose the first integer scale at which any summand places more than half
its mass in a translated cube. The previous scale controls every remaining
summand. Localized convolution and Esseen then give a recurrence for the
actual independent sum after removing the selected summand.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Convolution

namespace CircularLaw

def miroshnikovStepConstant : ℝ := 12 * (24 * Real.exp 1 / Real.pi)

theorem miroshnikovStepConstant_pos : 0 < miroshnikovStepConstant := by
  unfold miroshnikovStepConstant
  positivity

def miroshnikovConstant : ℝ := 4 * (miroshnikovStepConstant + 1)

theorem miroshnikovConstant_ge_two : 2 ≤ miroshnikovConstant := by
  unfold miroshnikovConstant
  linarith [miroshnikovStepConstant_pos]

theorem miroshnikov_cube_removal_step {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (hm : 2 ≤ Fintype.card ι) {r α : ℝ} (hr : 0 < r) (hα : α < 1 / 2)
    (hBound : ∀ i, cubeConcentration (μ i) r ≤ α) :
    ∃ q : ι, cubeConcentration (productSumLaw μ) r ≤
      miroshnikovStepConstant * α / Real.sqrt (Fintype.card ι - 1 : ℕ) +
        (1 / 2) * cubeConcentration
          (productSumLaw (fun i : {i : ι // i ≠ q} => μ i.val)) r := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨N, q, b, hN, hMass, hHalf⟩ :=
    exists_first_half_mass_cube μ hr (fun i => (hBound i).trans_lt hα)
  let ν := productSumLaw (fun i : {i : ι // i ≠ q} => μ i.val)
  have hCount : 1 ≤ Fintype.card {i : ι // i ≠ q} := by
    rw [card_remove_one q]
    omega
  have hEnlarged := median_cube_sum_bound
    (fun i : {i : ι // i ≠ q} => μ i.val) hCount hr hN (fun i => hHalf i.val)
  have hRadius : r + (N : ℝ) * r = ((N : ℝ) + 1) * r := by ring
  rw [← hRadius, card_remove_one q] at hEnlarged
  have hRecurrence := convolution_half_mass_cube_recurrence ν (μ q) b r
    ((N : ℝ) * r) hMass.le
  rw [← Measure.conv_comm, ← productSumLaw_remove μ q] at hRecurrence
  refine ⟨q, hRecurrence.trans ?_⟩
  refine add_le_add ?_ le_rfl
  have hαNonneg : 0 ≤ α := (cubeConcentration_nonneg (μ q) r).trans (hBound q)
  have h := mul_le_mul (hBound q) hEnlarged
    (cubeConcentration_nonneg ν (r + (N : ℝ) * r)) hαNonneg
  convert h using 1
  unfold miroshnikovStepConstant
  ring

theorem sqrt_predecessor_three_quarters {m : ℕ} (hm : 3 ≤ m) :
    (3 / 4 : ℝ) * Real.sqrt (m : ℝ) ≤ Real.sqrt (m - 1 : ℕ) := by
  have hCast : (m - 1 : ℕ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ m by omega)]
    norm_num
  have hmReal : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hSq := Real.sq_sqrt (show 0 ≤ (m : ℝ) by positivity)
  have hPredSq : Real.sqrt (m - 1 : ℕ) ^ 2 = (m : ℝ) - 1 :=
    (Real.sq_sqrt (show (0 : ℝ) ≤ (m - 1 : ℕ) by positivity)).trans hCast
  have hRoot := Real.sqrt_nonneg (m : ℝ)
  have hPredRoot := Real.sqrt_nonneg (m - 1 : ℕ)
  nlinarith

end CircularLaw
