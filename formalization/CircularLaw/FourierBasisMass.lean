import CircularLaw.SignedFourierMixing
import CircularLaw.BernoulliProjectionSmallBall
import Mathlib.MeasureTheory.Integral.Average

/-!
# Existence of a basis with large total coordinate mass

The ambient coordinate energies lie in [0,1] and sum to the subspace
dimension. Fair-sign Fourier mixing therefore has expected total l1
coordinate mass at least h*sqrt(h)/8. An actual sample supplies a genuine
orthonormal basis attaining this lower bound.
This is the average-mass input to the extremal spread-basis construction.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def basisCoordinateEnergy {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Submodule ℂ (EuclideanSpace ℂ ι)} (B : OrthonormalBasis κ ℂ V) (i : ι) : ℝ :=
  ∑ j, ‖(B j : EuclideanSpace ℂ ι) i‖ ^ 2

def subspaceBasisL1Mass {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Submodule ℂ (EuclideanSpace ℂ ι)} (B : OrthonormalBasis κ ℂ V) : ℝ :=
  ∑ j, ∑ i, ‖(B j : EuclideanSpace ℂ ι) i‖

theorem basis_coordinate_energy_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Submodule ℂ (EuclideanSpace ℂ ι)} (B : OrthonormalBasis κ ℂ V) (i : ι) :
    0 ≤ basisCoordinateEnergy B i := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem basis_coordinate_energy_eq_projection {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Submodule ℂ (EuclideanSpace ℂ ι)} (B : OrthonormalBasis κ ℂ V) (i : ι) :
    basisCoordinateEnergy B i = ‖V.starProjection (EuclideanSpace.single i 1)‖ ^ 2 := by
  classical
  have h := orthogonal_projection_basis_energy V B (EuclideanSpace.single i 1)
  simpa only [basisCoordinateEnergy, EuclideanSpace.inner_single_right, one_mul,
    Complex.norm_conj] using h.symm

theorem basis_coordinate_energy_le_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Submodule ℂ (EuclideanSpace ℂ ι)} (B : OrthonormalBasis κ ℂ V) (i : ι) :
    basisCoordinateEnergy B i ≤ 1 := by
  rw [basis_coordinate_energy_eq_projection]
  have h := V.norm_starProjection_apply_le (EuclideanSpace.single i (1 : ℂ))
  simp only [EuclideanSpace.norm_single, norm_one] at h
  nlinarith [norm_nonneg (V.starProjection (EuclideanSpace.single i 1))]

theorem basis_coordinate_energy_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Submodule ℂ (EuclideanSpace ℂ ι)} (B : OrthonormalBasis κ ℂ V) :
    (∑ i, basisCoordinateEnergy B i) = (Fintype.card κ : ℝ) := by
  unfold basisCoordinateEnergy
  rw [Finset.sum_comm]
  have hNorm (j : κ) : (∑ i, ‖(B j : EuclideanSpace ℂ ι) i‖ ^ 2) = 1 := by
    rw [← EuclideanSpace.norm_sq_eq]
    change ‖B j‖ ^ 2 = 1
    rw [B.orthonormal.norm_eq_one]
    norm_num
  simp_rw [hNorm]
  simp

theorem basis_coordinate_sqrt_energy_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Submodule ℂ (EuclideanSpace ℂ ι)} (B : OrthonormalBasis κ ℂ V) :
    (Fintype.card κ : ℝ) ≤ ∑ i, Real.sqrt (basisCoordinateEnergy B i) := by
  rw [← basis_coordinate_energy_sum B]
  apply Finset.sum_le_sum
  intro i _
  have hNonneg := basis_coordinate_energy_nonneg B i
  have hUpper := basis_coordinate_energy_le_one B i
  have hSquare := Real.sq_sqrt hNonneg
  have hRoot := Real.sqrt_nonneg (basisCoordinateEnergy B i)
  nlinarith

theorem signed_fourier_basis_mean_l1_mass {ι : Type*} [Fintype ι]
    {h : ℕ} [NeZero h] {V : Submodule ℂ (EuclideanSpace ℂ ι)}
    (B : OrthonormalBasis (ZMod h) ℂ V) :
    (h : ℝ) * Real.sqrt (h : ℝ) / 8 ≤
      ∫ x, subspaceBasisL1Mass (signedFourierBasis B x)
        ∂bernoulliCubeLaw (ZMod h) (1 / 2) (by norm_num) := by
  have hh : 0 < (h : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne h)
  have hRoot : 0 < Real.sqrt (h : ℝ) := Real.sqrt_pos.mpr hh
  have hSum : (h : ℝ) ≤ ∑ i, Real.sqrt (basisCoordinateEnergy B i) := by
    simpa only [ZMod.card] using basis_coordinate_sqrt_energy_sum B
  unfold subspaceBasisL1Mass
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  calc
    _ = (h : ℝ) * ((h : ℝ) / (8 * Real.sqrt (h : ℝ))) := by
      field_simp
      nlinarith only [Real.sq_sqrt hh.le]
    _ ≤ (h : ℝ) * ((∑ i, Real.sqrt (basisCoordinateEnergy B i)) / (8 * Real.sqrt (h : ℝ))) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hSum (by positivity)) hh.le
    _ = ∑ _j : ZMod h, ∑ i,
        Real.sqrt (basisCoordinateEnergy B i) / (8 * Real.sqrt (h : ℝ)) := by
      simp only [Finset.sum_div, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum (fun j _ => Finset.sum_le_sum
      (fun i _ => signed_fourier_coordinate_mean_norm V B j i))

theorem exists_basis_large_total_l1_mass {ι : Type*} [Fintype ι]
    {h : ℕ} [NeZero h] {V : Submodule ℂ (EuclideanSpace ℂ ι)}
    (B : OrthonormalBasis (ZMod h) ℂ V) :
    ∃ B' : OrthonormalBasis (ZMod h) ℂ V,
      (h : ℝ) * Real.sqrt (h : ℝ) / 8 ≤ subspaceBasisL1Mass B' := by
  obtain ⟨x, hx⟩ := exists_integral_le (μ := bernoulliCubeLaw (ZMod h) (1 / 2) (by norm_num))
    (f := fun x => subspaceBasisL1Mass (signedFourierBasis B x)) Integrable.of_finite
  exact ⟨signedFourierBasis B x, (signed_fourier_basis_mean_l1_mass B).trans hx⟩

end CircularLaw
