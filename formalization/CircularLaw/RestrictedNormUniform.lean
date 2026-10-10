import CircularLaw.RestrictedNormRetained
import CircularLaw.UniformSourceKernelConditions
import CircularLaw.SteepNetCardinalityFinite

/-!
# The retained `n^-100` tail uniformly over the source degree band

The existing absolute lower constant `C>=96` is already enough for the
norm proof's condition `103*log(n)<=9*d`. One threshold covers every
degree in the literal lower band and every deterministic retained set.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

theorem eventually_retainedCenteredNormBound_hundred_uniform {C : ℝ} (hC : 96 ≤ C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d → ∀ I : Finset (Fin n),
      uniformProbability (fun rows : RowSliceMatrix n d =>
        ¬RetainedCenteredNormBound I rows (rowSliceComplexNormConstant 100)) ≤
          1 / (n : ℝ) ^ 100 := by
  have hCPos : 0 < C := by linarith only [hC]
  filter_upwards [eventually_ge_atTop 2, eventually_source_kernel_conditions_uniform hCPos (1 + σ)]
    with n hn hConditions
  intro d hBand I
  have hCon := hConditions d hBand.1 hBand.2
  have hDims := source_kernel_dimension_twice_degree hCon
  have hdn : d ≤ n := by omega
  have hLog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hLower := mul_le_mul_of_nonneg_left hBand.1 (by norm_num : (0 : ℝ) ≤ 9)
  have hThreshold := mul_le_mul_of_nonneg_right (show (103 : ℝ) ≤ 9 * C by linarith only [hC]) hLog
  have hDegree : 103 * Real.log (n : ℝ) ≤ 9 * (d : ℝ) := by
    nlinarith only [hLower, hThreshold]
  exact retainedCenteredNormBound_failure_hundred hn hDims.2.1 hdn hDegree I

end CircularLaw
