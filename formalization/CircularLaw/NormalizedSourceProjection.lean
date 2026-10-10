import CircularLaw.NormalizedGraphThreshold
import CircularLaw.NormalizedLargeProjection
import CircularLaw.BernoulliSourceGraphExposure
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Actual Bernoulli projection bounds at normalized source thresholds

The actual leading-row kernel supplies its near-kernel estimate at the
actual singular scale. Both branches retain the sqrt(d) projection
factor. The small branch uses the doubled explicit source-power constant;
the large branch uses the source squared logarithm. In the guarded
exposure range the error tends to zero as epsilon tends to zero and
the degree tends to infinity.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix BigOperators NNReal InnerProductSpace Topology

namespace CircularLaw

def sourceNormalizedBernoulliLogIncrement (K β n d g : ℝ) : ℝ :=
  if g ≤ n * d ^ (-1 / 4 : ℝ) then sourceNormalizedGraphLogIncrement K β n d g
  else sourceLargeLogIncrement n g

def normalizedSourceProjectionFailureBound (ε d : ℝ) : ℝ :=
  bernoulliLargeProjectionConstant * (ε + 3 * d ^ (-1 / 4 : ℝ)) +
    4 * bernoulliScalarSmallBallConstant / Real.sqrt (Real.log (Real.log d))

theorem remaining_fraction_log_lower {n g ε : ℝ}
    (hn : 0 < n) (hg : 0 < g) (hFraction : g / n ≤ ε) (hε : ε ≤ Real.exp (-4)) :
    4 ≤ Real.log (n / g) := by
  have hLog := Real.log_le_log (div_pos hg hn) (hFraction.trans hε)
  rw [Real.log_exp, Real.log_div hg.ne' hn.ne'] at hLog
  rw [Real.log_div hn.ne' hg.ne']
  linarith

theorem normalized_source_projection_failure_bound_nonneg {ε d : ℝ}
    (hε : 0 ≤ ε) (hd : 0 ≤ d) : 0 ≤ normalizedSourceProjectionFailureBound ε d := by
  unfold normalizedSourceProjectionFailureBound
  exact add_nonneg (mul_nonneg bernoulli_large_projection_constant_pos.le
    (add_nonneg hε (mul_nonneg (by norm_num) (Real.rpow_nonneg hd _))))
    (div_nonneg (mul_nonneg (by norm_num) bernoulli_scalar_small_ball_constant_pos.le)
      (Real.sqrt_nonneg _))

theorem normalized_source_projection_failure_bound_tendsto_zero
    {α : Type*} {l : Filter α} {ε d : α → ℝ}
    (hε : Tendsto ε l (𝓝 0)) (hd : Tendsto d l atTop) :
    Tendsto (fun x => normalizedSourceProjectionFailureBound (ε x) (d x)) l (𝓝 0) := by
  have hPower : Tendsto (fun x => d x ^ (-1 / 4 : ℝ)) l (𝓝 0) := by
    simpa only [neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hd
  have hRoot : Tendsto (fun x => Real.sqrt (Real.log (Real.log (d x)))) l atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hd))
  have hTail : Tendsto (fun x =>
      4 * bernoulliScalarSmallBallConstant / Real.sqrt (Real.log (Real.log (d x)))) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hRoot
  simpa only [normalizedSourceProjectionFailureBound, mul_zero, zero_add] using
    ((hε.add (hPower.const_mul 3)).const_mul bernoulliLargeProjectionConstant).add hTail

set_option maxHeartbeats 1500000 in
theorem bernoulli_leading_kernel_projection_of_normalized_source_graph {N r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (hrm : r < m)
    (hProd : leadingRowSingularProduct (diagonalEmbeddedShift A e z) h ≠ 0)
    {K β d : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbient : m ≤ N) (hAmbientLower : (N : ℝ) / 2 ≤ (m : ℝ))
    (hGuard : (N - m) / 8 < m - r)
    (hRange : ((N - r : ℕ) : ℝ) ≤ (N : ℝ) * d ^ (-1 / 4 : ℝ))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K N d)
    (hUnique : MatrixUniqueExpansionBudget A e β N d
      (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin))
      (sourceGraphTerminalScale N d)) (hHeavy : MatrixHeavyRowBudget A β N d)
    (hScale : leadingKernelSingularScale r (diagonalEmbeddedShift A e z) ≤
      Real.sqrt d * Real.exp (-(N : ℝ) * sourceNormalizedGraphLogIncrement K β N d (N - r : ℕ)))
    (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      ‖(LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin).starProjection
        (bernoulliCubeVector x + w)‖ <
        Real.sqrt d * Real.exp (-(N : ℝ) * sourceNormalizedGraphLogIncrement K β N d (N - r : ℕ))} ≤
      4 * bernoulliScalarSmallBallConstant / Real.sqrt (Real.log (Real.log d)) := by
  have hNNat : 0 < N := by omega
  have hn : 0 < (N : ℝ) := by exact_mod_cast hNNat
  obtain ⟨hN, hTerminal⟩ := source_graph_exposure_degree_range hn hHalf hDegree hd
  obtain ⟨hEnergy, hRadius⟩ := leading_kernel_normalized_source_threshold_comparisons
    (diagonalEmbeddedShift A e z) h hrm hProd hK hβ hβOne hN hd hAmbient hGuard hRange
  have hThreshold : 0 ≤ Real.sqrt d * Real.exp
      (-(N : ℝ) * sourceNormalizedGraphLogIncrement K β N d (N - r : ℕ)) := by positivity
  have hSmall := ((sq_le_sq₀ (leading_kernel_singular_scale_nonneg _) hThreshold).mpr hScale).trans_lt hEnergy
  exact bernoulli_leading_kernel_projection_of_terminal_graph p hp hpPos hHalf A e z h hrm hProd
    hK hβ hβOne hn hTerminal hDegree (by exact_mod_cast hAmbient) hAmbientLower hz hzUpper
    hColumns hUnique hHeavy hSmall hThreshold hRadius w

set_option maxHeartbeats 1500000 in
theorem bernoulli_leading_kernel_projection_of_normalized_source_threshold {N r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (hrm : r < m)
    (hProd : leadingRowSingularProduct (diagonalEmbeddedShift A e z) h ≠ 0)
    {K β d ε : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbient : m ≤ N) (hAmbientLower : (N : ℝ) / 2 ≤ (m : ℝ))
    (hGuard : (N - m) / 8 < m - r)
    (hFraction : ((N - r : ℕ) : ℝ) / N ≤ ε) (hε : ε ≤ Real.exp (-4))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K N d)
    (hUnique : MatrixUniqueExpansionBudget A e β N d
      (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin))
      (sourceGraphTerminalScale N d)) (hHeavy : MatrixHeavyRowBudget A β N d)
    (hScale : leadingKernelSingularScale r (diagonalEmbeddedShift A e z) ≤
      Real.sqrt d * Real.exp (-(N : ℝ) * sourceNormalizedBernoulliLogIncrement K β N d (N - r : ℕ)))
    (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      ‖(LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin).starProjection
        (bernoulliCubeVector x + w)‖ <
        Real.sqrt d * Real.exp (-(N : ℝ) * sourceNormalizedBernoulliLogIncrement K β N d (N - r : ℕ))} ≤
      normalizedSourceProjectionFailureBound ε d := by
  have hNNat : 0 < N := by omega
  have hn : 0 < (N : ℝ) := by exact_mod_cast hNNat
  have hdPos : 0 < d := (Real.exp_pos _).trans_le hd
  have hg : 0 < ((N - r : ℕ) : ℝ) := by
    have hNat : 0 < N - r := by omega
    exact_mod_cast hNat
  have hEpsilon : 0 ≤ ε := (div_pos hg hn).le.trans hFraction
  unfold sourceNormalizedBernoulliLogIncrement at *
  by_cases hRange : ((N - r : ℕ) : ℝ) ≤ (N : ℝ) * d ^ (-1 / 4 : ℝ)
  · rw [if_pos hRange] at hScale ⊢
    have hProb := bernoulli_leading_kernel_projection_of_normalized_source_graph p hp hpPos hHalf A e z h hrm hProd
      hK hβ hβOne hd hDegree hAmbient hAmbientLower hGuard hRange hz hzUpper hColumns hUnique hHeavy hScale w
    exact hProb.trans (le_add_of_nonneg_left (mul_nonneg bernoulli_large_projection_constant_pos.le
      (add_nonneg hEpsilon (mul_nonneg (by norm_num) (Real.rpow_nonneg hdPos.le _)))))
  · rw [if_neg hRange]
    have hV : 0 < Module.finrank ℂ
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin) := by
      rw [leading_row_kernel_dimension _ h hProd]
      omega
    have hGap : ((N - r : ℕ) : ℝ) ≤ 9 * (Module.finrank ℂ
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin) : ℝ) := by
      rw [leading_row_kernel_dimension _ h hProd]
      exact_mod_cast exposure_global_gap_le_nine_local hAmbient hrm hGuard
    have hdOne : 1 ≤ (N : ℝ) * p := by rw [← hDegree]; linarith [Real.add_one_le_exp (4 : ℝ)]
    have hRangeLarge : (N : ℝ) * ((N : ℝ) * p) ^ (-1 / 4 : ℝ) ≤ ((N - r : ℕ) : ℝ) := by
      rw [← hDegree]
      exact (lt_of_not_ge hRange).le
    have hProb := bernoulli_projection_of_normalized_source_large_threshold p hp hpPos hHalf hNNat
      (by simpa only [Fintype.card_fin] using hAmbient) hdOne _ hV hg hGap hRangeLarge
      (remaining_fraction_log_lower hn hg hFraction hε) hFraction w
    rw [← hDegree] at hProb
    exact hProb.trans (le_add_of_nonneg_right (div_nonneg
      (mul_nonneg (by norm_num) bernoulli_scalar_small_ball_constant_pos.le) (Real.sqrt_nonneg _)))

end CircularLaw
