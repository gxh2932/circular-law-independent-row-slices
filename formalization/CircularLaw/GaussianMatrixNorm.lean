import CircularLaw.ComplexLatticeNet
import CircularLaw.ComplexHalfNetReduction
import CircularLaw.GaussianMatrixBilinearTail
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# An actual Gaussian matrix operator-norm bound

The two finite complex half-nets give at most an exponential number of
bilinear tests. Their actual Gaussian tails imply that the raw matrix
norm exceeds `128*sqrt(n)` with probability at most `exp(-36*n)`.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators InnerProductSpace Matrix Topology

namespace CircularLaw

theorem gaussian_matrix_operator_net_tail {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) :
    (gaussianSquareMatrixLaw n).real
      {x | 4 * r < ‖complexMatrixOperator (gaussianSquareMatrix x)‖} ≤
        ((complexHalfLatticeNet n).card : ℝ) ^ 2 * Real.exp (-(r / 4) ^ 2) := by
  let S := complexHalfLatticeNet n
  let B : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) → Set (GaussianSquareSample n) :=
    fun p => {x | r ≤ ‖⟪p.1, complexMatrixOperator (gaussianSquareMatrix x) p.2⟫_ℂ‖}
  have hSubset : {x : GaussianSquareSample n | 4 * r < ‖complexMatrixOperator (gaussianSquareMatrix x)‖} ⊆
      ⋃ p ∈ S ×ˢ S, B p := by
    intro x hx
    have hExists : ∃ u ∈ S, ∃ v ∈ S,
        r < ‖⟪u, complexMatrixOperator (gaussianSquareMatrix x) v⟫_ℂ‖ := by
      by_contra h
      push_neg at h
      have hBound := complex_operator_bound_of_half_nets S S
        (complex_half_lattice_net_cover hn) (complex_half_lattice_net_cover hn) hr.le
        (complexMatrixOperator (gaussianSquareMatrix x)) h
      exact not_lt_of_ge hBound hx
    obtain ⟨u, hu, v, hv, hLarge⟩ := hExists
    exact Set.mem_iUnion.mpr ⟨(u, v), Set.mem_iUnion.mpr
      ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hLarge.le⟩⟩
  calc
    _ ≤ ∑ p ∈ S ×ˢ S, (gaussianSquareMatrixLaw n).real (B p) :=
      (measureReal_mono (μ := gaussianSquareMatrixLaw n) hSubset (measure_ne_top _ _)).trans
        (measureReal_biUnion_finset_le _ _)
    _ ≤ ∑ _p ∈ S ×ˢ S, Real.exp (-(r / 4) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      exact gaussian_matrix_bilinear_radial_tail p.1 p.2
        (complex_half_lattice_net_norm_le hn (Finset.mem_product.mp hp).1)
        (complex_half_lattice_net_norm_le hn (Finset.mem_product.mp hp).2) hr
    _ = _ := by simp only [Finset.sum_const, Finset.card_product, nsmul_eq_mul, Nat.cast_mul, pow_two]; rfl

theorem gaussian_matrix_operator_norm_tail {n : ℕ} (hn : 0 < n) :
    (gaussianSquareMatrixLaw n).real
      {x | 128 * Real.sqrt (n : ℝ) < ‖complexMatrixOperator (gaussianSquareMatrix x)‖} ≤
        Real.exp (-36 * (n : ℝ)) := by
  have hRoot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h := gaussian_matrix_operator_net_tail hn (r := 32 * Real.sqrt (n : ℝ)) (by positivity)
  have hThreshold : 4 * (32 * Real.sqrt (n : ℝ)) = 128 * Real.sqrt (n : ℝ) := by ring
  have hPower : ((32 * Real.sqrt (n : ℝ)) / 4) ^ 2 = 64 * (n : ℝ) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  rw [hThreshold, hPower] at h
  apply h.trans
  calc
    _ ≤ Real.exp (14 * (n : ℝ)) ^ 2 * Real.exp (-(64 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (complex_half_lattice_net_card_exponential n) 2)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring

theorem gaussian_matrix_operator_norm_bad_probability_tendsto :
    Tendsto (fun n : ℕ => (gaussianSquareMatrixLaw n).real
      {x | 128 * Real.sqrt (n : ℝ) < ‖complexMatrixOperator (gaussianSquareMatrix x)‖})
      atTop (𝓝 0) := by
  have hLimit : Tendsto (fun n : ℕ => Real.exp (-36 * (n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg
      (by norm_num : (-36 : ℝ) < 0))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLimit
    (Eventually.of_forall (fun _ => measureReal_nonneg))
    ((eventually_gt_atTop 0).mono (fun _ hn => gaussian_matrix_operator_norm_tail hn))

end CircularLaw
