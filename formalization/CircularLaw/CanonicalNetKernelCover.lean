import CircularLaw.CenteredSliceAction
import CircularLaw.CoordinateClassRestriction

/-!
# Deterministic covering of shifted kernel vectors by the actual net

The retained centered norm bound is an explicit event hypothesis.
Every continuous kernel vector gives its literal canonical approximant
and a scalar in the checked finite mean grid. The spectral window
produces an explicit coefficient in the source Euclidean radius.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def canonicalNetCoverCoefficient (B Z₀ : ℝ) : ℝ := Real.sqrt 2 * (2 * B + 3 * Z₀ + 1)

theorem canonicalNetCoverCoefficient_pos {B Z₀ : ℝ} (hB : 0 ≤ B) (hZ : 0 ≤ Z₀) :
    0 < canonicalNetCoverCoefficient B Z₀ := by
  unfold canonicalNetCoverCoefficient
  positivity

theorem canonical_kernel_net_raw_error {n d k : ℕ} (hn : 0 < n) (hk : 0 < k) (hd : 0 < d)
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d) {B : ℝ} (hB : 0 ≤ B)
    (hNorm : RetainedCenteredNormBound I rows B) (x : Fin n → ℂ)
    (hKernel : (retainedShiftedMatrix I ζ rows).mulVec x = 0) :
    indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) (fun j => canonicalApprox k (x j))
      (canonicalNetShift I d ζ (fun j => canonicalApprox k (x j))
        (canonicalApprox (k * d) (canonicalErrorMean k x))) ≤
      (B * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt 2 * Real.sqrt n / (k : ℝ)) +
        Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d) * ((d : ℝ) + ‖ζ‖)) := by
  let β := canonicalApprox (k * d) (canonicalErrorMean k x)
  let γ := (β - canonicalErrorMean k x) * ((d : ℂ) - ζ)
  have hGamma : ‖γ‖ ≤ Real.sqrt 2 / ((k : ℝ) * d) * ((d : ℝ) + ‖ζ‖) := by
    dsimp only [γ]
    rw [norm_mul]
    have hMean := canonicalErrorMean_fine_grid_error hk hd x
    rw [norm_sub_rev] at hMean
    exact mul_le_mul hMean (by simpa only [Complex.norm_natCast] using norm_sub_le (d : ℂ) ζ)
      (norm_nonneg _) (by positivity)
  have hCard : (Fintype.card I : ℝ) ≤ n := by
    rw [Fintype.card_coe]
    exact_mod_cast (Finset.card_le_univ I).trans_eq (Fintype.card_fin n)
  have hConstant : ‖(WithLp.toLp 2 (fun _ : I => γ) : EuclideanSpace ℂ I)‖ ≤
      Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d) * ((d : ℝ) + ‖ζ‖)) :=
    (euclidean_norm_le_uniform _ (by positivity) (fun _ => hGamma)).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hCard) (by positivity))
  have hAction := retainedShiftedMatrix_zero_sum_norm_bound I ζ rows B hNorm
    (centeredCanonicalError k x) (centeredCanonicalError_sum hn k x)
  have hAction' := hAction.trans (mul_le_mul_of_nonneg_left
    (centeredCanonicalError_euclidean_bound hn hk x) (by positivity : 0 ≤ B * Real.sqrt d + ‖ζ‖))
  have hFunction : (fun i : I => rowLinearForm (rows i.val) (fun j => canonicalApprox k (x j)) +
      canonicalNetShift I d ζ (fun j => canonicalApprox k (x j)) β i) =
        -((retainedShiftedMatrix I ζ rows).mulVec (centeredCanonicalError k x)) + (fun _ => γ) := by
    funext i
    exact canonicalNetShift_kernel_identity k I ζ rows x hKernel β i
  change ‖(WithLp.toLp 2 (fun i : I => rowLinearForm (rows i.val) (fun j => canonicalApprox k (x j)) +
    canonicalNetShift I d ζ (fun j => canonicalApprox k (x j)) β i) : EuclideanSpace ℂ I)‖ ≤ _
  rw [hFunction, WithLp.toLp_add, WithLp.toLp_neg]
  apply (norm_add_le _ _).trans
  rw [norm_neg]
  exact add_le_add hAction' hConstant

theorem canonical_net_error_budget {n d k : ℕ} (hd : 0 < d) (hk : 0 < k)
    {B Z₀ : ℝ} (hZ : 0 ≤ Z₀) (ζ : ℂ) (hShift : ‖ζ‖ ≤ Z₀ * Real.sqrt d) :
    (B * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt 2 * Real.sqrt n / (k : ℝ)) +
      Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d) * ((d : ℝ) + ‖ζ‖)) ≤
        canonicalNetCoverCoefficient B Z₀ * Real.sqrt ((d : ℝ) * n) / k := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hDOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hRootOne : (1 : ℝ) ≤ Real.sqrt d := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hDOne
  have hRootLe : Real.sqrt d ≤ (d : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hdR.le).mp
    rw [Real.sq_sqrt hdR.le]
    nlinarith only [hDOne]
  have hMain : (B * Real.sqrt d + ‖ζ‖) * (2 * Real.sqrt 2 * Real.sqrt n / (k : ℝ)) ≤
      2 * Real.sqrt 2 * (B + Z₀) * Real.sqrt ((d : ℝ) * n) / k := by
    apply (mul_le_mul_of_nonneg_right (add_le_add_right hShift _) (by positivity)).trans
    rw [Real.sqrt_mul hdR.le]
    exact le_of_eq (by ring)
  have hShiftD := hShift.trans (mul_le_mul_of_nonneg_left hRootLe hZ)
  have hScalar : Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d) * ((d : ℝ) + ‖ζ‖)) ≤
      Real.sqrt 2 * (1 + Z₀) * Real.sqrt ((d : ℝ) * n) / k := by
    calc
      _ ≤ Real.sqrt n * (Real.sqrt 2 / ((k : ℝ) * d) * ((1 + Z₀) * d)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_left (by linarith only [hShiftD]) (by positivity)
      _ = Real.sqrt 2 * (1 + Z₀) * Real.sqrt n / k := by field_simp
      _ ≤ _ := by
        rw [Real.sqrt_mul hdR.le]
        have hRoot := mul_le_mul_of_nonneg_right hRootOne (Real.sqrt_nonneg (n : ℝ))
        simp only [one_mul] at hRoot
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRoot (by positivity)) hkR.le
  apply (add_le_add hMain hScalar).trans
  unfold canonicalNetCoverCoefficient
  exact le_of_eq (by ring)

theorem canonical_kernel_net_cover {n d k : ℕ} (hn : 0 < n) (hd : 0 < d) (hk : 0 < k)
    {B Z₀ R : ℝ} (hB : 0 ≤ B) (hZ : 0 ≤ Z₀)
    (hDegree : canonicalNetCoverCoefficient B Z₀ ≤ R * Real.log d)
    (I : Finset (Fin n)) (ζ : ℂ) (hShift : ‖ζ‖ ≤ Z₀ * Real.sqrt d) (rows : RowSliceMatrix n d)
    (hNorm : RetainedCenteredNormBound I rows B) (X : Set (Fin n → ℂ))
    (x : Fin n → ℂ) (hx : x ∈ X) (hKernel : (retainedShiftedMatrix I ζ rows).mulVec x = 0) :
    ∃ y ∈ canonicalApproxFamily k X, ∃ β ∈ scalarMeanGrid k d,
      indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y (canonicalNetShift I d ζ y β) ≤
        R * Real.log d * Real.sqrt ((d : ℝ) * n) / k := by
  refine ⟨(fun j => canonicalApprox k (x j)), ⟨x, hx, rfl⟩,
    canonicalApprox (k * d) (canonicalErrorMean k x), canonicalErrorMean_fine_grid_mem hn hk hd x, ?_⟩
  apply (canonical_kernel_net_raw_error hn hk hd I ζ rows hB hNorm x hKernel).trans
  apply (canonical_net_error_budget hd hk hZ ζ hShift).trans
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hDegree (Real.sqrt_nonneg _))
    (Nat.cast_nonneg k)

end CircularLaw
