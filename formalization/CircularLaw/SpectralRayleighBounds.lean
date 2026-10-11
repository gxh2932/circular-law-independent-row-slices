import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Interval.Finset.Fin

/-!
# Rayleigh bounds in the ordered spectral basis

The spectral quadratic form is the eigenvalue-weighted coordinate energy.
Vanishing before an index therefore gives its upper Rayleigh bound. The
head-coordinate kernel loses at most the number of removed coordinates.
These checked facts supply the dimension argument for eigenvalue comparison.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators InnerProductSpace

namespace CircularLaw

theorem complex_real_inner_real_mul (a : ℝ) (z : ℂ) :
    (⟪(a : ℂ) * z, z⟫_ℂ).re = a * ‖z‖ ^ 2 := by
  rw [RCLike.inner_apply]
  change (z * (starRingEnd ℂ) ((a : ℂ) * z)).re = _
  rw [map_mul, Complex.conj_ofReal]
  have hProduct : z * ((a : ℂ) * (starRingEnd ℂ) z) =
      (a : ℂ) * (z * (starRingEnd ℂ) z) := by ring
  rw [hProduct, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

section Symmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {n : ℕ} {T : E →ₗ[ℂ] E}

theorem symmetric_quadratic_spectral_sum (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (v : E) :
    (⟪T v, v⟫_ℂ).re = ∑ i : Fin n, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr v i‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.inner_map_map, PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hT.eigenvectorBasis_apply_self_apply hn v i]
  exact complex_real_inner_real_mul _ _

theorem spectral_coordinate_energy (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (v : E) :
    ‖v‖ ^ 2 = ∑ i : Fin n, ‖(hT.eigenvectorBasis hn).repr v i‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.norm_map v, EuclideanSpace.norm_sq_eq]

theorem symmetric_quadratic_le_tail (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (j : Fin n) (v : E)
    (hZero : ∀ i : Fin n, i < j → (hT.eigenvectorBasis hn).repr v i = 0) :
    (⟪T v, v⟫_ℂ).re ≤ hT.eigenvalues hn j * ‖v‖ ^ 2 := by
  rw [symmetric_quadratic_spectral_sum hT hn, spectral_coordinate_energy hT hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hij : i < j
  · rw [hZero i hij, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn (le_of_not_gt hij)) (sq_nonneg _)

theorem symmetric_quadratic_ge_head (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (j : Fin n) (v : E)
    (hZero : ∀ i : Fin n, j < i → (hT.eigenvectorBasis hn).repr v i = 0) :
    hT.eigenvalues hn j * ‖v‖ ^ 2 ≤ (⟪T v, v⟫_ℂ).re := by
  rw [symmetric_quadratic_spectral_sum hT hn, spectral_coordinate_energy hT hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hij : j < i
  · rw [hZero i hij, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn (le_of_not_gt hij)) (sq_nonneg _)

def spectralHeadCoordinateMap (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n) (j : Fin n) :
    E →ₗ[ℂ] (Finset.Iio j → ℂ) :=
  LinearMap.pi (fun i => (PiLp.projₗ (𝕜 := ℂ) (β := fun _ : Fin n => ℂ) 2 i.val).comp
    (hT.eigenvectorBasis hn).repr.toLinearEquiv.toLinearMap)

theorem spectralHeadCoordinateMap_apply (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (j : Fin n) (v : E) (i : Finset.Iio j) :
    spectralHeadCoordinateMap hT hn j v i = (hT.eigenvectorBasis hn).repr v i.val := rfl

theorem spectral_head_kernel_vanishes (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (j : Fin n) (v : E) (hv : v ∈ LinearMap.ker (spectralHeadCoordinateMap hT hn j)) :
    ∀ i : Fin n, i < j → (hT.eigenvectorBasis hn).repr v i = 0 := by
  intro i hi
  exact congrFun (LinearMap.mem_ker.mp hv) (⟨i, Finset.mem_Iio.mpr hi⟩ : Finset.Iio j)

theorem spectral_head_kernel_dimension (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (j : Fin n) :
    n ≤ Module.finrank ℂ (LinearMap.ker (spectralHeadCoordinateMap hT hn j)) + j.val := by
  have hRank := (spectralHeadCoordinateMap hT hn j).finrank_range_add_finrank_ker
  have hRange : Module.finrank ℂ (LinearMap.range (spectralHeadCoordinateMap hT hn j)) ≤ j.val := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fin.card_Iio] using
      (LinearMap.range (spectralHeadCoordinateMap hT hn j)).finrank_le
  omega

theorem eigenvalue_lower_bound_of_subspace (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (j : Fin n) (W : Submodule ℂ E) (hDim : j.val < Module.finrank ℂ W)
    {r : ℝ} (hRayleigh : ∀ v ∈ W, r * ‖v‖ ^ 2 ≤ (⟪T v, v⟫_ℂ).re) :
    r ≤ hT.eigenvalues hn j := by
  let V := LinearMap.ker (spectralHeadCoordinateMap hT hn j)
  have hDimV := spectral_head_kernel_dimension hT hn j
  change n ≤ Module.finrank ℂ V + j.val at hDimV
  have hIntersection : ∃ v : E, v ∈ W ∧ v ∈ V ∧ v ≠ 0 := by
    by_contra! hAll
    have hDisjoint : Disjoint W V := Submodule.disjoint_def.mpr hAll
    have hRanks := Submodule.finrank_add_finrank_le_of_disjoint hDisjoint
    omega
  obtain ⟨v, hvW, hvV, hv0⟩ := hIntersection
  have hUpper := symmetric_quadratic_le_tail hT hn j v (spectral_head_kernel_vanishes hT hn j v hvV)
  have hNorm : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv0)
  exact (mul_le_mul_iff_left₀ hNorm).mp ((hRayleigh v hvW).trans hUpper)

end Symmetric

end CircularLaw
