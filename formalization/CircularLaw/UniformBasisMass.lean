import CircularLaw.ExtremalBasisMass
import CircularLaw.BasisPairRotation

/-!
# Uniform ambient coordinate mass in an orthonormal basis

At a basis maximizing total coordinate mass, a pair rotation forces any
two basis-vector masses to differ by at most a factor of four. The signed
Fourier average then gives sqrt(h)/32 for every basis vector.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

theorem maximal_basis_l1_mass_comparison {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Submodule ℂ (EuclideanSpace ℂ ι)} (B : OrthonormalBasis κ ℂ V)
    (hMax : ∀ C : OrthonormalBasis κ ℂ V, subspaceBasisL1Mass C ≤ subspaceBasisL1Mass B)
    (i j : κ) :
    coordinateL1Mass (B j : EuclideanSpace ℂ ι) / 4 ≤
      coordinateL1Mass (B i : EuclideanSpace ℂ ι) := by
  by_cases hij : i = j
  · subst j
    nlinarith [coordinate_l1_mass_nonneg (B i : EuclideanSpace ℂ ι)]
  · have hBound := hMax (basisPairRotation B hij)
    rw [basis_pair_rotation_l1_mass B hij] at hBound
    have hPair := basis_pair_rotation_pair_l1_lower B hij
    linarith

theorem exists_basis_uniform_l1_mass {ι : Type*} [Fintype ι]
    {h : ℕ} [NeZero h] {V : Submodule ℂ (EuclideanSpace ℂ ι)}
    (B : OrthonormalBasis (ZMod h) ℂ V) :
    ∃ C : OrthonormalBasis (ZMod h) ℂ V, ∀ j,
      Real.sqrt (h : ℝ) / 32 ≤ coordinateL1Mass (C j : EuclideanSpace ℂ ι) := by
  obtain ⟨C, hMax⟩ := exists_basis_maximal_l1_mass B
  obtain ⟨D, hD⟩ := exists_basis_large_total_l1_mass B
  have hTotal := hD.trans (hMax D)
  have hh : 0 < (h : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne h)
  refine ⟨C, ?_⟩
  intro i
  have hUpper : subspaceBasisL1Mass C ≤
      ∑ _j : ZMod h, 4 * coordinateL1Mass (C i : EuclideanSpace ℂ ι) := by
    apply Finset.sum_le_sum
    intro j _
    have hPair := maximal_basis_l1_mass_comparison C hMax i j
    change coordinateL1Mass (C j : EuclideanSpace ℂ ι) ≤ _
    linarith
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at hUpper
  apply (mul_le_mul_iff_right₀ hh).mp
  nlinarith

end CircularLaw
