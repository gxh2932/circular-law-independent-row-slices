import CircularLaw.PairedSliceSampling
import CircularLaw.FairBooleanSmallBall
import CircularLaw.FiniteDiskConcentration

/-!
# Slice small balls reduced to the number of separated pairs

The conditional bound uses the actual independent fair choices. Averaging
over uniform injective pair samples isolates the event that too few pairs
are separated. The probability estimate for that event is not assumed to
be proved by this reduction.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def pairedSeparatedCoordinates {n d : ℕ} (y : Fin n → ℂ) (ρ : ℝ)
    (e : Fin d ⊕ Fin d ↪ Fin n) : Finset (Fin d) :=
  Finset.univ.filter (fun j => ρ ≤ ‖y (e (Sum.inr j)) - y (e (Sum.inl j))‖)

theorem paired_slice_conditional_small_ball {n d : ℕ} (e : Fin d ⊕ Fin d ↪ Fin n)
    (y : Fin n → ℂ) (S : Finset (Fin d)) (hS : S.Nonempty) {ρ r : ℝ} (hρ : 0 < ρ)
    (hLarge : ∀ j ∈ S, ρ ≤ ‖y (e (Sum.inr j)) - y (e (Sum.inl j))‖)
    (hr : ρ / 2 ≤ r) (z : ℂ) :
    uniformProbability (fun x : Fin d → Bool => ‖rowLinearForm (pairedSlice e x) y - z‖ ≤ r) ≤
      bernoulliScalarSmallBallConstant * (r / ρ) / Real.sqrt ((S.card : ℝ) / 2) := by
  have h := fair_boolean_linear_form_small_ball
    (fun j => y (e (Sum.inr j)) - y (e (Sum.inl j))) S hS hρ hLarge hr
    (z - ∑ j, y (e (Sum.inl j)))
  convert h using 1
  congr 1
  funext x
  rw [paired_slice_linear_form]
  congr 2
  ring

theorem paired_slice_conditional_small_ball_of_count {n d k : ℕ}
    (hk : 0 < k) (e : Fin d ⊕ Fin d ↪ Fin n) (y : Fin n → ℂ)
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : ρ / 2 ≤ r)
    (hCount : k ≤ (pairedSeparatedCoordinates y ρ e).card) (z : ℂ) :
    uniformProbability (fun x : Fin d → Bool => ‖rowLinearForm (pairedSlice e x) y - z‖ ≤ r) ≤
      bernoulliScalarSmallBallConstant * (r / ρ) / Real.sqrt ((k : ℝ) / 2) := by
  have hrNonneg : 0 ≤ r := (by positivity : 0 ≤ ρ / 2).trans hr
  have h := paired_slice_conditional_small_ball e y (pairedSeparatedCoordinates y ρ e)
    (Finset.card_pos.mp (hk.trans_le hCount)) hρ
    (fun _ hj => (Finset.mem_filter.mp hj).2) hr z
  exact h.trans (div_le_div_of_nonneg_left
    (mul_nonneg bernoulli_scalar_small_ball_constant_pos.le (by positivity))
    (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by exact_mod_cast hCount) (by norm_num))))

theorem row_slice_small_ball_le_pair_failure {n d k : ℕ} (hSize : 2 * d ≤ n)
    (hk : 0 < k) (y : Fin n → ℂ) {ρ r : ℝ} (hρ : 0 < ρ) (hr : ρ / 2 ≤ r) (z : ℂ) :
    uniformProbability (fun S : RowSlice n d => ‖rowLinearForm S y - z‖ ≤ r) ≤
      bernoulliScalarSmallBallConstant * (r / ρ) / Real.sqrt ((k : ℝ) / 2) +
        uniformProbability (fun e : Fin d ⊕ Fin d ↪ Fin n =>
          (pairedSeparatedCoordinates y ρ e).card < k) := by
  haveI : Nonempty (Fin d ⊕ Fin d ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_sum,
      Fintype.card_fin] using (by omega : d + d ≤ n))
  let q := bernoulliScalarSmallBallConstant * (r / ρ) / Real.sqrt ((k : ℝ) / 2)
  have hrNonneg : 0 ≤ r := (by positivity : 0 ≤ ρ / 2).trans hr
  have hq : 0 ≤ q := div_nonneg
    (mul_nonneg bernoulli_scalar_small_ball_constant_pos.le (div_nonneg hrNonneg hρ.le))
    (Real.sqrt_nonneg _)
  rw [uniform_paired_slice_conditioning hSize]
  calc
    _ ≤ finiteMean (fun e : Fin d ⊕ Fin d ↪ Fin n =>
      q + if (pairedSeparatedCoordinates y ρ e).card < k then (1 : ℝ) else 0) := by
      apply finiteMean_mono
      intro e
      by_cases hCount : k ≤ (pairedSeparatedCoordinates y ρ e).card
      · simpa only [not_lt.mpr hCount, if_false, add_zero] using
          paired_slice_conditional_small_ball_of_count hk e y hρ hr hCount z
      · simp only [Nat.lt_of_not_ge hCount, if_true]
        exact (uniformProbability_le_one _).trans (by linarith)
    _ = _ := by rw [finiteMean_add, finiteMean_const, finiteMean_indicator]

theorem row_slice_concentration_le_pair_failure {n d k : ℕ} (hSize : 2 * d ≤ n)
    (hk : 0 < k) (y : Fin n → ℂ) {ρ r : ℝ} (hρ : 0 < ρ) (hr : ρ / 2 ≤ r) :
    rowSliceDiskConcentration (d := d) y r ≤
      bernoulliScalarSmallBallConstant * (r / ρ) / Real.sqrt ((k : ℝ) / 2) +
        uniformProbability (fun e : Fin d ⊕ Fin d ↪ Fin n =>
          (pairedSeparatedCoordinates y ρ e).card < k) := by
  apply finiteDiskConcentration_le
  intro z
  simpa only [rowLinearForm_eq_support_sum] using
    row_slice_small_ball_le_pair_failure hSize hk y hρ hr z

end CircularLaw
