import CircularLaw.RegularizedRowSingularFormula

/-!
# Removing the manuscript row-volume regularization

When every actual row singular value is at least tau, ridge regularization
changes the log volume by at most k*eta^2/(2*tau^2). The exact source choice
eta=tau/n gives normalized error at most 1/(2*n^2), with no asymptotic
replacement of the integer row count.
-/

noncomputable section
open Classical
open scoped Matrix BigOperators

namespace CircularLaw

theorem regularized_scalar_log_error_eq {s : ℝ} (hs : 0 < s) (η : ℝ) :
    (1 / 2 : ℝ) * Real.log (η ^ 2 + s ^ 2) - Real.log s =
      (1 / 2 : ℝ) * Real.log (1 + η ^ 2 / s ^ 2) := by
  have hFactor : η ^ 2 + s ^ 2 = s ^ 2 * (1 + η ^ 2 / s ^ 2) := by
    field_simp [hs.ne']
    ring
  have hPos : 0 < 1 + η ^ 2 / s ^ 2 := by positivity
  rw [hFactor, Real.log_mul (sq_pos_of_pos hs).ne' hPos.ne', Real.log_pow]
  ring

theorem regularized_scalar_log_error_bounds {τ s : ℝ} (hτ : 0 < τ) (hLower : τ ≤ s) (η : ℝ) :
    0 ≤ (1 / 2 : ℝ) * Real.log (η ^ 2 + s ^ 2) - Real.log s ∧
      (1 / 2 : ℝ) * Real.log (η ^ 2 + s ^ 2) - Real.log s ≤ η ^ 2 / (2 * τ ^ 2) := by
  have hs := hτ.trans_le hLower
  rw [regularized_scalar_log_error_eq hs]
  have hRatio : 0 ≤ η ^ 2 / s ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hRatioUpper : η ^ 2 / s ^ 2 ≤ η ^ 2 / τ ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hτ)
      (pow_le_pow_left₀ hτ.le hLower 2)
  constructor
  · exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  · have hLog := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + η ^ 2 / s ^ 2)
    calc
      _ ≤ (1 / 2 : ℝ) * (η ^ 2 / τ ^ 2) := by linarith
      _ = _ := by ring

theorem regularized_row_potential_log_volume_bounds {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ)
    (hLower : ∀ j, τ ≤ orderedMatrixSingularValues A j) :
    0 ≤ regularizedRowPotential A η - matrixRowLogVolume A ∧
      regularizedRowPotential A η - matrixRowLogVolume A ≤
        (Fintype.card ι : ℝ) * η ^ 2 / (2 * τ ^ 2) := by
  rw [regularized_row_potential_eq_singular_log_sum A hη, matrixRowLogVolume,
    ← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg (fun j _ => (regularized_scalar_log_error_bounds hτ (hLower j) η).1)
  · calc
      _ ≤ ∑ _j : Fin (Fintype.card ι), η ^ 2 / (2 * τ ^ 2) :=
        Finset.sum_le_sum (fun j _ => (regularized_scalar_log_error_bounds hτ (hLower j) η).2)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem regularized_row_log_removal_at_tau_over_dimension {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) (hmn : m ≤ n) {τ : ℝ} (hτ : 0 < τ)
    (hLower : ∀ j, τ ≤ orderedMatrixSingularValues A j) :
    0 ≤ (regularizedRowPotential A (τ / n) - matrixRowLogVolume A) / n ∧
      (regularizedRowPotential A (τ / n) - matrixRowLogVolume A) / n ≤ 1 / (2 * (n : ℝ) ^ 2) := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hBounds := regularized_row_potential_log_volume_bounds A (div_pos hτ hnReal) hτ hLower
  simp only [Fintype.card_fin] at hBounds
  have hM : (m : ℝ) ≤ n := by exact_mod_cast hmn
  refine ⟨div_nonneg hBounds.1 hnReal.le, ?_⟩
  have hScale : ((m : ℝ) * (τ / n) ^ 2 / (2 * τ ^ 2)) / n = (m : ℝ) / (2 * (n : ℝ) ^ 3) := by
    field_simp
  calc
    _ ≤ ((m : ℝ) * (τ / n) ^ 2 / (2 * τ ^ 2)) / n :=
      div_le_div_of_nonneg_right hBounds.2 hnReal.le
    _ = (m : ℝ) / (2 * (n : ℝ) ^ 3) := hScale
    _ ≤ (n : ℝ) / (2 * (n : ℝ) ^ 3) := div_le_div_of_nonneg_right hM (by positivity)
    _ = _ := by field_simp

end CircularLaw
