import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Complex operator bounds from actual half-nets

Approximating a normalized vector absorbs half its norm. Applying this
first in the range and then in the domain bounds the operator norm by
four times the largest tested complex inner product.
-/

noncomputable section
open Classical
open scoped InnerProductSpace

namespace CircularLaw

theorem complex_vector_bound_of_half_net {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset E)
    (hCover : ∀ x : E, ‖x‖ ≤ 1 → ∃ u ∈ S, ‖x - u‖ ≤ 1 / 2)
    {T : ℝ} (hT : 0 ≤ T) (w : E) (hNet : ∀ u ∈ S, ‖⟪u, w⟫_ℂ‖ ≤ T) :
    ‖w‖ ≤ 2 * T := by
  by_cases hw : w = 0
  · simp only [hw, norm_zero]
    positivity
  have hNorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let x : E := ((‖w‖⁻¹ : ℝ) : ℂ) • w
  have hx : ‖x‖ ≤ 1 := by
    simp only [x, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNorm),
      inv_mul_cancel₀ hNorm.ne', le_refl]
  have hInner : ‖⟪x, w⟫_ℂ‖ = ‖w‖ := by
    change ‖⟪((‖w‖⁻¹ : ℝ) : ℂ) • w, w⟫_ℂ‖ = ‖w‖
    rw [inner_smul_left, norm_mul]
    change ‖star ((‖w‖⁻¹ : ℝ) : ℂ)‖ * ‖⟪w, w⟫_ℂ‖ = ‖w‖
    rw [norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hNorm), inner_self_eq_norm_sq_to_K, norm_pow]
    change ‖w‖⁻¹ * ‖(‖w‖ : ℂ)‖ ^ 2 = ‖w‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNorm]
    field_simp
  obtain ⟨u, hu, hClose⟩ := hCover x hx
  have hSplit : ⟪x, w⟫_ℂ = ⟪u, w⟫_ℂ + ⟪x - u, w⟫_ℂ := by
    rw [inner_sub_left]
    ring
  have hError : ‖⟪x - u, w⟫_ℂ‖ ≤ (1 / 2) * ‖w‖ :=
    (norm_inner_le_norm (𝕜 := ℂ) (x - u) w).trans
      (mul_le_mul_of_nonneg_right hClose hNorm.le)
  have hBound : ‖w‖ ≤ T + (1 / 2) * ‖w‖ := by
    calc
      _ = ‖⟪x, w⟫_ℂ‖ := hInner.symm
      _ ≤ ‖⟪u, w⟫_ℂ‖ + ‖⟪x - u, w⟫_ℂ‖ := by rw [hSplit]; exact norm_add_le _ _
      _ ≤ _ := add_le_add (hNet u hu) hError
  linarith

theorem complex_linear_bound_of_half_net {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (S : Finset E) (hCover : ∀ x : E, ‖x‖ ≤ 1 → ∃ u ∈ S, ‖x - u‖ ≤ 1 / 2)
    {T : ℝ} (hT : 0 ≤ T) (f : E →L[ℂ] F) (hNet : ∀ u ∈ S, ‖f u‖ ≤ T) :
    ‖f‖ ≤ 2 * T := by
  have hBound : ‖f‖ ≤ T + ‖f‖ / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨u, hu, hClose⟩ := hCover x hx.le
    have hSplit : f x = f u + f (x - u) := by rw [map_sub]; abel
    calc
      _ ≤ ‖f u‖ + ‖f (x - u)‖ := by rw [hSplit]; exact norm_add_le _ _
      _ ≤ T + ‖f‖ * (1 / 2) := add_le_add (hNet u hu)
        ((f.le_opNorm (x - u)).trans (mul_le_mul_of_nonneg_left hClose (norm_nonneg f)))
      _ = _ := by ring
  linarith

theorem complex_operator_bound_of_half_nets {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (S : Finset F) (R : Finset E)
    (hS : ∀ x : F, ‖x‖ ≤ 1 → ∃ u ∈ S, ‖x - u‖ ≤ 1 / 2)
    (hR : ∀ y : E, ‖y‖ ≤ 1 → ∃ v ∈ R, ‖y - v‖ ≤ 1 / 2)
    {T : ℝ} (hT : 0 ≤ T) (f : E →L[ℂ] F)
    (hNet : ∀ u ∈ S, ∀ v ∈ R, ‖⟪u, f v⟫_ℂ‖ ≤ T) : ‖f‖ ≤ 4 * T := by
  have hRight : ∀ v ∈ R, ‖f v‖ ≤ 2 * T := by
    intro v hv
    exact complex_vector_bound_of_half_net S hS hT (f v) (fun u hu => hNet u hu v hv)
  have h := complex_linear_bound_of_half_net R hR (by positivity) f hRight
  linarith

end CircularLaw
