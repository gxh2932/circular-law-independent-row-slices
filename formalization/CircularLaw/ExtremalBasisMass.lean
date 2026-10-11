import CircularLaw.FourierBasisMass
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# An orthonormal basis maximizing total ambient coordinate mass

Orthonormal frames of a fixed finite size form a closed bounded subset of
a finite-dimensional space. A continuous total l1 coordinate mass therefore
attains its maximum. Every full-size frame spans the original subspace.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

theorem orthonormal_frames_isClosed {κ E : Type*} [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    IsClosed {b : κ → E | Orthonormal ℂ b} := by
  classical
  have hSet : {b : κ → E | Orthonormal ℂ b} =
      ⋂ i : κ, ⋂ j : κ, {b : κ → E | ⟪b i, b j⟫_ℂ = if i = j then 1 else 0} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact orthonormal_iff_ite (𝕜 := ℂ) (v := b)
  rw [hSet]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  exact isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const

theorem orthonormal_frames_isCompact {κ E : Type*} [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] :
    IsCompact {b : κ → E | Orthonormal ℂ b} := by
  classical
  apply (isCompact_closedBall (0 : κ → E) 1).of_isClosed_subset orthonormal_frames_isClosed
  intro b hb
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (fun i => (Orthonormal.norm_eq_one (𝕜 := ℂ) hb i).le)

theorem exists_basis_maximal_l1_mass {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Submodule ℂ (EuclideanSpace ℂ ι)} (B : OrthonormalBasis κ ℂ V) :
    ∃ B' : OrthonormalBasis κ ℂ V, ∀ C : OrthonormalBasis κ ℂ V,
      subspaceBasisL1Mass C ≤ subspaceBasisL1Mass B' := by
  classical
  let f := fun b : κ → V => ∑ j, ∑ i, ‖(b j : EuclideanSpace ℂ ι) i‖
  have hContinuous : Continuous f := by
    unfold f
    fun_prop
  obtain ⟨b, hb, hMax⟩ := (orthonormal_frames_isCompact (E := V)).exists_isMaxOn
    ⟨B, B.orthonormal⟩ hContinuous.continuousOn
  have hon : Orthonormal ℂ b := hb
  let B' := OrthonormalBasis.mk hon
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis B.toBasis).symm).ge
  refine ⟨B', ?_⟩
  intro C
  have h := hMax C.orthonormal
  simpa only [subspaceBasisL1Mass, B', OrthonormalBasis.coe_mk, f] using h

end CircularLaw
