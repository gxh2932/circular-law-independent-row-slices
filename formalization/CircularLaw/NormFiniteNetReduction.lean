import CircularLaw.NormMeanProjection
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Finite quarter-net control of a real operator

Two successive approximations give the factor `16/9`, bounded above by
two. The nets are actual finite sets and their covering hypotheses are
explicit; the lattice construction supplies those hypotheses later.
-/

noncomputable section
open Classical
open scoped InnerProductSpace

namespace CircularLaw

theorem norm_vector_bound_of_quarter_net {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : Finset E)
    (hCover : ∀ x : E, ‖x‖ ≤ 1 → ∃ u ∈ S, ‖x - u‖ ≤ 1 / 4)
    {T : ℝ} (hT : 0 ≤ T) (w : E) (hNet : ∀ u ∈ S, |⟪u, w⟫_ℝ| ≤ T) :
    ‖w‖ ≤ (4 / 3) * T := by
  by_cases hw : w = 0
  · simp only [hw, norm_zero]
    positivity
  have hNorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let x : E := ‖w‖⁻¹ • w
  have hx : ‖x‖ ≤ 1 := by
    simp only [x, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNorm),
      inv_mul_cancel₀ hNorm.ne', le_refl]
  have hInner : ⟪x, w⟫_ℝ = ‖w‖ := by
    simp only [x, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  obtain ⟨u, hu, hClose⟩ := hCover x hx
  have hSplit : ⟪x, w⟫_ℝ = ⟪u, w⟫_ℝ + ⟪x - u, w⟫_ℝ := by
    rw [inner_sub_left]
    ring
  have hError : |⟪x - u, w⟫_ℝ| ≤ (1 / 4) * ‖w‖ := by
    have hCauchy : |⟪x - u, w⟫_ℝ| ≤ ‖x - u‖ * ‖w‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (x - u) w
    exact hCauchy.trans (mul_le_mul_of_nonneg_right hClose hNorm.le)
  have hBound : ‖w‖ ≤ T + (1 / 4) * ‖w‖ := by
    calc
      _ = |⟪x, w⟫_ℝ| := by rw [hInner, abs_of_pos hNorm]
      _ ≤ |⟪u, w⟫_ℝ| + |⟪x - u, w⟫_ℝ| := by rw [hSplit]; exact abs_add_le _ _
      _ ≤ _ := add_le_add (hNet u hu) hError
  linarith

theorem norm_linear_bound_of_quarter_net {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Finset E)
    (hCover : ∀ x : E, ‖x‖ ≤ 1 → ∃ u ∈ S, ‖x - u‖ ≤ 1 / 4)
    {T : ℝ} (hT : 0 ≤ T) (f : E →L[ℝ] F) (hNet : ∀ u ∈ S, ‖f u‖ ≤ T) :
    ‖f‖ ≤ (4 / 3) * T := by
  have hBound : ‖f‖ ≤ T + ‖f‖ / 4 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨u, hu, hClose⟩ := hCover x hx.le
    have hSplit : f x = f u + f (x - u) := by rw [map_sub]; abel
    calc
      _ ≤ ‖f u‖ + ‖f (x - u)‖ := by rw [hSplit]; exact norm_add_le _ _
      _ ≤ T + ‖f‖ * (1 / 4) :=
        add_le_add (hNet u hu) ((f.le_opNorm (x - u)).trans
          (mul_le_mul_of_nonneg_left hClose (norm_nonneg f)))
      _ = _ := by ring
  linarith

theorem norm_operator_bound_of_quarter_nets {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (S : Finset F) (R : Finset E)
    (hS : ∀ x : F, ‖x‖ ≤ 1 → ∃ u ∈ S, ‖x - u‖ ≤ 1 / 4)
    (hR : ∀ y : E, ‖y‖ ≤ 1 → ∃ v ∈ R, ‖y - v‖ ≤ 1 / 4)
    {T : ℝ} (hT : 0 ≤ T) (f : E →L[ℝ] F)
    (hNet : ∀ u ∈ S, ∀ v ∈ R, |⟪u, f v⟫_ℝ| ≤ T) : ‖f‖ ≤ 2 * T := by
  have hRight : ∀ v ∈ R, ‖f v‖ ≤ (4 / 3) * T := by
    intro v hv
    exact norm_vector_bound_of_quarter_net S hS hT (f v) (fun u hu => hNet u hu v hv)
  have h := norm_linear_bound_of_quarter_net R hR (by positivity) f hRight
  linarith

end CircularLaw
