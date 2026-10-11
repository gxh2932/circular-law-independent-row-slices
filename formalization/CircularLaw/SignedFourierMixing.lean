import CircularLaw.FlatFourierBasis
import CircularLaw.RademacherLinearMoments

/-!
# Orthonormal basis mixing by fair signs and a flat Fourier matrix

Every sign sample produces a genuine orthonormal basis. Each ambient
coordinate is an actual complex Rademacher sum, with an explicitly computed
coefficient energy and a checked mean-norm lower bound.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

theorem rademacher_value_norm (b : Bool) : ‖rademacherValue b‖ = 1 := by
  cases b <;> simp [rademacherValue]

theorem rademacher_value_mul_self (b : Bool) : rademacherValue b * rademacherValue b = 1 := by
  cases b <;> simp [rademacherValue]

def rademacherSignIsometry {ι : Type*} [Fintype ι] (x : ι → Bool) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι where
  toFun v := WithLp.toLp 2 (fun i => rademacherValue (x i) * v i)
  invFun v := WithLp.toLp 2 (fun i => rademacherValue (x i) * v i)
  left_inv v := by
    ext i
    simp only [← mul_assoc, rademacher_value_mul_self, one_mul]
  right_inv v := by
    ext i
    simp only [← mul_assoc, rademacher_value_mul_self, one_mul]
  map_add' v w := by ext i; simp [mul_add]
  map_smul' c v := by ext i; simp [smul_eq_mul, mul_left_comm]
  norm_map' v := by
    change ‖WithLp.toLp 2 (fun i => rademacherValue (x i) * v i)‖ = ‖v‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.norm_sq_eq, norm_mul, rademacher_value_norm, one_mul]

theorem rademacher_sign_isometry_apply {ι : Type*} [Fintype ι] (x : ι → Bool)
    (v : EuclideanSpace ℂ ι) (i : ι) :
    rademacherSignIsometry x v i = rademacherValue (x i) * v i := rfl

def signedFourierBasis {h : ℕ} [NeZero h] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (B : OrthonormalBasis (ZMod h) ℂ E) (x : ZMod h → Bool) :
    OrthonormalBasis (ZMod h) ℂ E :=
  ((flatFourierBasis h).map (rademacherSignIsometry x)).map B.repr.symm

theorem signed_fourier_basis_repr {h : ℕ} [NeZero h] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (B : OrthonormalBasis (ZMod h) ℂ E)
    (x : ZMod h → Bool) (j i : ZMod h) :
    B.repr (signedFourierBasis B x j) i = rademacherValue (x i) * flatFourierMatrix h i j := by
  simp only [signedFourierBasis, OrthonormalBasis.map_apply,
    LinearIsometryEquiv.apply_symm_apply, rademacher_sign_isometry_apply, flat_fourier_basis_apply]

theorem signed_fourier_basis_coordinate {ι : Type*} [Fintype ι] {h : ℕ} [NeZero h]
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (B : OrthonormalBasis (ZMod h) ℂ V)
    (x : ZMod h → Bool) (j : ZMod h) (i : ι) :
    (signedFourierBasis B x j : EuclideanSpace ℂ ι) i =
      rademacherLinearForm (fun k => flatFourierMatrix h k j * (B k : EuclideanSpace ℂ ι) i) x := by
  conv_lhs => rw [← B.sum_repr (signedFourierBasis B x j)]
  simp only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, signed_fourier_basis_repr, rademacherLinearForm]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem signed_fourier_coordinate_coefficient_energy {ι : Type*} [Fintype ι]
    {h : ℕ} [NeZero h] (V : Submodule ℂ (EuclideanSpace ℂ ι))
    (B : OrthonormalBasis (ZMod h) ℂ V) (j : ZMod h) (i : ι) :
    (∑ k, ‖flatFourierMatrix h k j * (B k : EuclideanSpace ℂ ι) i‖ ^ 2) =
      ((Real.sqrt (h : ℝ))⁻¹) ^ 2 * ∑ k, ‖(B k : EuclideanSpace ℂ ι) i‖ ^ 2 := by
  simp_rw [norm_mul, flat_fourier_matrix_entry_norm, mul_pow]
  rw [← Finset.mul_sum]

theorem signed_fourier_coordinate_mean_norm {ι : Type*} [Fintype ι]
    {h : ℕ} [NeZero h] (V : Submodule ℂ (EuclideanSpace ℂ ι))
    (B : OrthonormalBasis (ZMod h) ℂ V) (j : ZMod h) (i : ι) :
    Real.sqrt (∑ k, ‖(B k : EuclideanSpace ℂ ι) i‖ ^ 2) / (8 * Real.sqrt (h : ℝ)) ≤
      ∫ x, ‖(signedFourierBasis B x j : EuclideanSpace ℂ ι) i‖
        ∂bernoulliCubeLaw (ZMod h) (1 / 2) (by norm_num) := by
  have hBound := rademacher_linear_form_mean_norm_lower
    (fun k => flatFourierMatrix h k j * (B k : EuclideanSpace ℂ ι) i)
  rw [signed_fourier_coordinate_coefficient_energy V B j i,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr (Real.sqrt_nonneg _))] at hBound
  simp_rw [signed_fourier_basis_coordinate V B]
  convert hBound using 1
  ring

end CircularLaw
