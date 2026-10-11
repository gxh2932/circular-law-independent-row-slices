import CircularLaw.UniformBasisMass

/-!
# An orthonormal basis with uniform coordinate spread

In an h-dimensional complex subspace of an n-dimensional coordinate
space, every vector of a suitable orthonormal basis has at least h/4096
coordinates of norm at least sqrt(h)/(64*n). This proves basis existence
with explicit absolute constants, including one-dimensional subspaces.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def coordinateSpreadSet {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) (ρ : ℝ) :
    Finset ι := Finset.univ.filter (fun i => ρ ≤ ‖v i‖)

theorem coordinate_spread_set_mem {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (ρ : ℝ) (i : ι) :
    i ∈ coordinateSpreadSet v ρ ↔ ρ ≤ ‖v i‖ := by
  simp only [coordinateSpreadSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem coordinate_l1_mass_le_spread_mass {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    coordinateL1Mass v ≤ (∑ i ∈ coordinateSpreadSet v ρ, ‖v i‖) +
      (Fintype.card ι : ℝ) * ρ := by
  have hPoint (i : ι) : ‖v i‖ ≤ (if ρ ≤ ‖v i‖ then ‖v i‖ else 0) + ρ := by
    by_cases hi : ρ ≤ ‖v i‖
    · simp only [if_pos hi]
      linarith
    · simp only [if_neg hi, zero_add]
      exact (lt_of_not_ge hi).le
  have hSum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hPoint i)
  simpa only [coordinateL1Mass, coordinateSpreadSet, Finset.sum_filter,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hSum

theorem unit_vector_subset_l1_square_le_card {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (hNorm : ‖v‖ = 1) (S : Finset ι) :
    (∑ i ∈ S, ‖v i‖) ^ 2 ≤ (S.card : ℝ) := by
  have hEnergy : (∑ i, ‖v i‖ ^ 2) = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hNorm]
    norm_num
  have hSubset : (∑ i ∈ S, ‖v i‖ ^ 2) ≤ 1 := by
    rw [← hEnergy]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => sq_nonneg ‖v i‖)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => ‖v i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul] at hCS
  exact hCS.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) S.card])

theorem unit_vector_coordinate_spread {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) (hNorm : ‖v‖ = 1)
    {h : ℕ} (hn : 0 < Fintype.card ι)
    (hMass : Real.sqrt (h : ℝ) / 32 ≤ coordinateL1Mass v) :
    (h : ℝ) / 4096 ≤
      ((coordinateSpreadSet v (Real.sqrt (h : ℝ) / (64 * Fintype.card ι))).card : ℝ) := by
  have hnReal : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hn
  have hRoot := Real.sqrt_nonneg (h : ℝ)
  have hSquare := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) h)
  have hMul : (Fintype.card ι : ℝ) *
      (Real.sqrt (h : ℝ) / (64 * Fintype.card ι)) = Real.sqrt (h : ℝ) / 64 := by
    field_simp
  have hSmall := coordinate_l1_mass_le_spread_mass v
    (div_nonneg hRoot (by positivity : (0 : ℝ) ≤ 64 * Fintype.card ι))
  rw [hMul] at hSmall
  have hLarge : Real.sqrt (h : ℝ) / 64 ≤
      ∑ i ∈ coordinateSpreadSet v (Real.sqrt (h : ℝ) / (64 * Fintype.card ι)), ‖v i‖ := by
    linarith
  have hCS := unit_vector_subset_l1_square_le_card v hNorm
    (coordinateSpreadSet v (Real.sqrt (h : ℝ) / (64 * Fintype.card ι)))
  nlinarith

theorem exists_zmod_basis_uniform_coordinate_spread {ι : Type*} [Fintype ι]
    {h : ℕ} [NeZero h] {V : Submodule ℂ (EuclideanSpace ℂ ι)}
    (B : OrthonormalBasis (ZMod h) ℂ V) :
    ∃ C : OrthonormalBasis (ZMod h) ℂ V, ∀ j,
      (h : ℝ) / 4096 ≤ ((coordinateSpreadSet (C j : EuclideanSpace ℂ ι)
        (Real.sqrt (h : ℝ) / (64 * Fintype.card ι))).card : ℝ) := by
  have hCard : h ≤ Fintype.card ι := by
    calc
      h = Module.finrank ℂ V := by rw [Module.finrank_eq_card_basis B.toBasis, ZMod.card]
      _ ≤ Module.finrank ℂ (EuclideanSpace ℂ ι) := V.finrank_le
      _ = Fintype.card ι := finrank_euclideanSpace
  have hn := lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne h)) hCard
  obtain ⟨C, hC⟩ := exists_basis_uniform_l1_mass B
  refine ⟨C, fun j => ?_⟩
  exact unit_vector_coordinate_spread (C j : EuclideanSpace ℂ ι) (C.norm_eq_one j) hn (hC j)

theorem exists_basis_uniform_coordinate_spread {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Submodule ℂ (EuclideanSpace ℂ ι)} (B : OrthonormalBasis κ ℂ V)
    (hκ : 0 < Fintype.card κ) :
    ∃ C : OrthonormalBasis κ ℂ V, ∀ j,
      (Fintype.card κ : ℝ) / 4096 ≤ ((coordinateSpreadSet (C j : EuclideanSpace ℂ ι)
        (Real.sqrt (Fintype.card κ : ℝ) / (64 * Fintype.card ι))).card : ℝ) := by
  classical
  letI : NeZero (Fintype.card κ) := ⟨Nat.ne_of_gt hκ⟩
  let e : κ ≃ ZMod (Fintype.card κ) :=
    (Fintype.equivFin κ).trans (ZMod.finEquiv (Fintype.card κ)).toEquiv
  obtain ⟨C, hC⟩ := exists_zmod_basis_uniform_coordinate_spread (B.reindex e)
  refine ⟨C.reindex e.symm, fun j => ?_⟩
  simpa only [OrthonormalBasis.reindex_apply, Equiv.symm_symm] using hC (e j)

theorem exists_subspace_uniform_coordinate_spread {ι : Type*} [Fintype ι]
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (hV : 0 < Module.finrank ℂ V) :
    ∃ C : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V, ∀ j,
      (Module.finrank ℂ V : ℝ) / 4096 ≤ ((coordinateSpreadSet (C j : EuclideanSpace ℂ ι)
        (Real.sqrt (Module.finrank ℂ V : ℝ) / (64 * Fintype.card ι))).card : ℝ) := by
  simpa only [Fintype.card_fin] using
    exists_basis_uniform_coordinate_spread (stdOrthonormalBasis ℂ V) (by simpa using hV)

end CircularLaw
