import CircularLaw.SpectralSubspaceComparison

/-!
# Shifted spectral comparisons with the exact codimension loss

Intersecting a leading spectral subspace with the range of a coordinate
isometry loses at most the codimension. Intersecting with the kernel of
a map to an `r`-dimensional space loses at most `r` dimensions. Rayleigh
bounds then give the complementary interlacing inequalities required
when rows and columns are deleted in hermitization.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped InnerProductSpace

namespace CircularLaw

theorem subspace_intersection_finrank_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (V W : Submodule ℂ E) :
    Module.finrank ℂ V + Module.finrank ℂ W ≤
      Module.finrank ℂ E + Module.finrank ℂ (V ⊓ W : Submodule ℂ E) := by
  have h := V.finrank_sup_add_finrank_inf_eq W
  have hSup := (V ⊔ W).finrank_le
  omega

theorem symmetric_shifted_eigenvalues_le_under_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {m n : ℕ} {S : E →ₗ[ℂ] E} {T : F →ₗ[ℂ] F}
    (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hm : Module.finrank ℂ E = m) (hn : Module.finrank ℂ F = n) (hmn : m ≤ n)
    (L : E →ₗᵢ[ℂ] F)
    (hQuadratic : ∀ v : E, (⟪T (L v), L v⟫_ℂ).re ≤ (⟪S v, v⟫_ℂ).re)
    (i : Fin m) (j : Fin n) (hIndex : j.val = i.val + (n - m)) :
    hT.eigenvalues hn j ≤ hS.eigenvalues hm i := by
  let V := spectralLeadingSubspace hT hn j
  let W := V.comap L.toLinearMap
  have hMap : W.map L.toLinearMap = V ⊓ LinearMap.range L.toLinearMap := by
    simpa only [inf_comm] using Submodule.map_comap_eq L.toLinearMap V
  have hRank : Module.finrank ℂ (W.map L.toLinearMap) = Module.finrank ℂ W :=
    (Submodule.equivMapOfInjective L.toLinearMap L.injective W).finrank_eq.symm
  have hRange : Module.finrank ℂ (LinearMap.range L.toLinearMap) = m := by
    rw [LinearMap.finrank_range_of_inj L.injective, hm]
  have hDim := subspace_intersection_finrank_bound V (LinearMap.range L.toLinearMap)
  rw [← hMap, hRank, hRange, hn] at hDim
  have hV : Module.finrank ℂ V = j.val + 1 := spectral_leading_subspace_dimension hT hn j
  rw [hV] at hDim
  apply eigenvalue_lower_bound_of_subspace hS hm i W
  · omega
  · intro v hv
    have hvV : L v ∈ V := hv
    have hRayleigh := spectral_leading_subspace_rayleigh hT hn j (L v) hvV
    rw [L.norm_map] at hRayleigh
    exact hRayleigh.trans (hQuadratic v)

theorem symmetric_shifted_eigenvalues_le_on_kernel
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {n r : ℕ} {S T : E →ₗ[ℂ] E}
    (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (hr : Module.finrank ℂ F = r) (D : E →ₗ[ℂ] F)
    (hQuadratic : ∀ v ∈ LinearMap.ker D, (⟪T v, v⟫_ℂ).re ≤ (⟪S v, v⟫_ℂ).re)
    (i j : Fin n) (hIndex : j.val = i.val + r) :
    hT.eigenvalues hn j ≤ hS.eigenvalues hn i := by
  let V := spectralLeadingSubspace hT hn j
  let W := V ⊓ LinearMap.ker D
  have hNull := D.finrank_range_add_finrank_ker
  have hRange : Module.finrank ℂ (LinearMap.range D) ≤ r := by
    simpa only [hr] using (LinearMap.range D).finrank_le
  have hDim := subspace_intersection_finrank_bound V (LinearMap.ker D)
  have hV : Module.finrank ℂ V = j.val + 1 := spectral_leading_subspace_dimension hT hn j
  rw [hV, hn] at hDim
  apply eigenvalue_lower_bound_of_subspace hS hn i W
  · change i.val < Module.finrank ℂ (V ⊓ LinearMap.ker D : Submodule ℂ E)
    rw [hn] at hNull
    omega
  · intro v hv
    exact (spectral_leading_subspace_rayleigh hT hn j v hv.1).trans (hQuadratic v hv.2)

end CircularLaw
