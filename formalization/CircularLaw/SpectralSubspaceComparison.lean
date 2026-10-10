import CircularLaw.SpectralRayleighBounds

/-!
# Ordered eigenvalue comparison through leading spectral subspaces

The first `j+1` eigenvectors span a subspace of exactly that dimension.
The quadratic form there is at least its `j`th eigenvalue times the
norm squared. Combining this with the tail-kernel dimension argument
proves ordered eigenvalue comparison from quadratic-form domination.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators InnerProductSpace

namespace CircularLaw

section Symmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {n : ℕ} {T S : E →ₗ[ℂ] E}

def spectralLeadingSubspace (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n) (j : Fin n) :
    Submodule ℂ E :=
  Submodule.span ℂ (Set.range (fun i : Finset.Iic j => (hT.eigenvectorBasis hn) i.val))

theorem spectral_leading_subspace_dimension (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (j : Fin n) : Module.finrank ℂ (spectralLeadingSubspace hT hn j) = j.val + 1 := by
  have hLI := (hT.eigenvectorBasis hn).toBasis.linearIndependent.comp
    (fun i : Finset.Iic j => i.val) Subtype.val_injective
  simpa only [spectralLeadingSubspace, Fintype.card_coe, Fin.card_Iic] using finrank_span_eq_card hLI

theorem spectral_leading_subspace_vanishes (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (j : Fin n) (v : E) (hv : v ∈ spectralLeadingSubspace hT hn j) :
    ∀ k : Fin n, j < k → (hT.eigenvectorBasis hn).repr v k = 0 := by
  intro k hjk
  change v ∈ Submodule.span ℂ (Set.range (fun i : Finset.Iic j => (hT.eigenvectorBasis hn) i.val)) at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    have hik : i.val ≠ k := ne_of_lt ((Finset.mem_Iic.mp i.property).trans_lt hjk)
    simp only [OrthonormalBasis.repr_self, EuclideanSpace.single_apply, if_neg hik.symm]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, PiLp.add_apply, hx, hy, add_zero]
  | smul a x _ hx => simp only [map_smul, PiLp.smul_apply, hx, smul_zero]

theorem spectral_leading_subspace_rayleigh (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (j : Fin n) (v : E) (hv : v ∈ spectralLeadingSubspace hT hn j) :
    hT.eigenvalues hn j * ‖v‖ ^ 2 ≤ (⟪T v, v⟫_ℂ).re :=
  symmetric_quadratic_ge_head hT hn j v (spectral_leading_subspace_vanishes hT hn j v hv)

theorem symmetric_ordered_eigenvalues_le_of_quadratic (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n)
    (hQuadratic : ∀ v : E, (⟪S v, v⟫_ℂ).re ≤ (⟪T v, v⟫_ℂ).re) (j : Fin n) :
    hS.eigenvalues hn j ≤ hT.eigenvalues hn j := by
  apply eigenvalue_lower_bound_of_subspace hT hn j (spectralLeadingSubspace hS hn j)
  · rw [spectral_leading_subspace_dimension]
    omega
  · intro v hv
    exact (spectral_leading_subspace_rayleigh hS hn j v hv).trans (hQuadratic v)

end Symmetric

theorem symmetric_ordered_eigenvalues_le_under_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {m n : ℕ} {S : E →ₗ[ℂ] E} {T : F →ₗ[ℂ] F}
    (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hm : Module.finrank ℂ E = m) (hn : Module.finrank ℂ F = n)
    (L : E →ₗᵢ[ℂ] F)
    (hQuadratic : ∀ v : E, (⟪S v, v⟫_ℂ).re ≤ (⟪T (L v), L v⟫_ℂ).re)
    (i : Fin m) (j : Fin n) (hIndex : i.val = j.val) :
    hS.eigenvalues hm i ≤ hT.eigenvalues hn j := by
  let W := spectralLeadingSubspace hS hm i
  have hRank : Module.finrank ℂ (W.map L.toLinearMap) = Module.finrank ℂ W :=
    (Submodule.equivMapOfInjective L.toLinearMap L.injective W).finrank_eq.symm
  apply eigenvalue_lower_bound_of_subspace hT hn j (W.map L.toLinearMap)
  · rw [hRank]
    change j.val < Module.finrank ℂ (spectralLeadingSubspace hS hm i)
    rw [spectral_leading_subspace_dimension, hIndex]
    omega
  · rintro v ⟨w, hw, rfl⟩
    change hS.eigenvalues hm i * ‖L w‖ ^ 2 ≤ (⟪T (L w), L w⟫_ℂ).re
    rw [L.norm_map]
    exact (spectral_leading_subspace_rayleigh hS hm i w hw).trans (hQuadratic w)

end CircularLaw
