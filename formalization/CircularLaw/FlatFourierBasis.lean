import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A flat orthonormal Fourier basis in every positive dimension

Every entry of the unitary Fourier matrix has modulus 1/sqrt(h).
The resulting basis permits mixing an arbitrary subspace basis without
requiring its dimension to be a power of two.
-/

noncomputable section
open Classical
open scoped BigOperators InnerProductSpace

namespace CircularLaw

def flatFourierMatrix (h : ℕ) [NeZero h] : Matrix (ZMod h) (ZMod h) ℂ :=
  fun i j => (Real.sqrt (h : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (i * j)

theorem finite_fourier_character_sum (h : ℕ) [NeZero h] (z : ZMod h) :
    (∑ i : ZMod h, ZMod.stdAddChar (i * z)) = if z = 0 then (h : ℂ) else 0 := by
  by_cases hz : z = 0
  · simp [hz, ZMod.card]
  · rw [if_neg hz]
    simpa only [mul_comm] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar h hz))

theorem finite_fourier_character_inner (h : ℕ) [NeZero h] (i j k : ZMod h) :
    star (ZMod.stdAddChar (k * i)) * ZMod.stdAddChar (k * j) =
      ZMod.stdAddChar (k * (j - i)) := by
  rw [Complex.star_def, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem flat_fourier_matrix_entry_norm (h : ℕ) [NeZero h] (i j : ZMod h) :
    ‖flatFourierMatrix h i j‖ = (Real.sqrt (h : ℝ))⁻¹ := by
  simp only [flatFourierMatrix, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), AddChar.norm_apply, mul_one]

theorem flat_fourier_matrix_conjTranspose_mul (h : ℕ) [NeZero h] :
    (flatFourierMatrix h).conjTranspose * flatFourierMatrix h = 1 := by
  have hh : 0 < (h : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne h)
  have hSqrt : (Real.sqrt (h : ℝ) : ℂ) ^ 2 = (h : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hh.le
  have hCoeff : ((Real.sqrt (h : ℝ) : ℂ)⁻¹) ^ 2 * (h : ℂ) = 1 := by
    rw [← hSqrt, ← mul_pow, inv_mul_cancel₀ (by exact_mod_cast (Real.sqrt_pos.mpr hh).ne'), one_pow]
  have hStarCoeff : star ((Real.sqrt (h : ℝ) : ℂ)⁻¹) = (Real.sqrt (h : ℝ) : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, flatFourierMatrix, star_mul, hStarCoeff]
  have hEntry (k : ZMod h) :
      star (ZMod.stdAddChar (k * i)) * (Real.sqrt (h : ℝ) : ℂ)⁻¹ *
        ((Real.sqrt (h : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (k * j)) =
      ((Real.sqrt (h : ℝ) : ℂ)⁻¹) ^ 2 * ZMod.stdAddChar (k * (j - i)) := by
    rw [← finite_fourier_character_inner h i j k]
    ring
  simp_rw [hEntry]
  rw [← Finset.mul_sum, finite_fourier_character_sum]
  by_cases hij : i = j
  · subst j
    simp only [sub_self, Matrix.one_apply_eq, if_true]
    exact hCoeff
  · have hDiff : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
    simp [hDiff, hij]

def flatFourierVectors (h : ℕ) [NeZero h] (j : ZMod h) : EuclideanSpace ℂ (ZMod h) :=
  WithLp.toLp 2 (fun i => flatFourierMatrix h i j)

theorem flat_fourier_vectors_orthonormal (h : ℕ) [NeZero h] :
    Orthonormal ℂ (flatFourierVectors h) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hEntry := congrArg (fun M : Matrix (ZMod h) (ZMod h) ℂ => M i j)
    (flat_fourier_matrix_conjTranspose_mul h)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    flatFourierVectors, PiLp.inner_apply, RCLike.inner_apply, PiLp.toLp_apply, mul_comm] using hEntry

def flatFourierBasis (h : ℕ) [NeZero h] :
    OrthonormalBasis (ZMod h) ℂ (EuclideanSpace ℂ (ZMod h)) :=
  OrthonormalBasis.mk (flat_fourier_vectors_orthonormal h)
    ((flat_fourier_vectors_orthonormal h).linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp)).ge

theorem flat_fourier_basis_apply (h : ℕ) [NeZero h] (j i : ZMod h) :
    flatFourierBasis h j i = flatFourierMatrix h i j := by
  simp only [flatFourierBasis, OrthonormalBasis.coe_mk, flatFourierVectors, PiLp.toLp_apply]

end CircularLaw
