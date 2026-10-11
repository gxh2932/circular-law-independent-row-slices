import CircularLaw.BernoulliSourceGraphExposure
import CircularLaw.SourceLargeProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Both branches of the actual source-scale Bernoulli exposure step

The large branch uses the squared-log threshold, and the small branch
uses the degree and remaining-size eighth powers. The moving barrier
discharges the local/global dimension comparison. The resulting actual
failure probability is uniform in the retained rank and tends to zero
as the degree tends to infinity. Graph probabilities and the adapted
alternating process are separate remaining obligations.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix BigOperators NNReal InnerProductSpace Topology

namespace CircularLaw

def sourceBernoulliLogIncrement (K β n d g : ℝ) : ℝ :=
  if g ≤ n * d ^ (-1 / 4 : ℝ) then sourceGraphLogIncrement K β n d g
  else sourceLargeLogIncrement n g

def sourceExposureFailureBound (d : ℝ) : ℝ :=
  sourceLargeExposureConstant * d ^ (-1 / 4 : ℝ) +
    4 * bernoulliScalarSmallBallConstant / Real.sqrt (Real.log (Real.log d))

theorem source_exposure_failure_bound_nonneg {d : ℝ} (hd : 0 ≤ d) :
    0 ≤ sourceExposureFailureBound d := by
  unfold sourceExposureFailureBound
  exact add_nonneg (mul_nonneg source_large_exposure_constant_pos.le (Real.rpow_nonneg hd _))
    (div_nonneg (mul_nonneg (by norm_num) bernoulli_scalar_small_ball_constant_pos.le)
      (Real.sqrt_nonneg _))

theorem source_exposure_failure_bound_tendsto_zero :
    Tendsto sourceExposureFailureBound atTop (𝓝 0) := by
  have hPower : Tendsto (fun d : ℝ => d ^ (-1 / 4 : ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have hRoot : Tendsto (fun d : ℝ => Real.sqrt (Real.log (Real.log d))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  have hTail : Tendsto (fun d : ℝ =>
      4 * bernoulliScalarSmallBallConstant / Real.sqrt (Real.log (Real.log d))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hRoot
  simpa only [sourceExposureFailureBound, mul_zero, zero_add] using
    (hPower.const_mul sourceLargeExposureConstant).add hTail

set_option maxHeartbeats 1500000 in
theorem bernoulli_row_log_failure_of_source_large_threshold {N r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (h : r ≤ a) (hrm : r < m)
    (hOld : 0 < leadingRowSingularProduct A h) (hAmbient : m ≤ N)
    (hd : 1 ≤ (N : ℝ) * p) (hGuard : (N - m) / 8 < m - r)
    (hRange : (N : ℝ) * ((N : ℝ) * p) ^ (-1 / 4 : ℝ) ≤ ((N - r : ℕ) : ℝ))
    (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      leadingRowLogPrefix A h / N + sourceLargeLogIncrement N (N - r : ℕ) <
        insertedLeadingLogPrefix A h (bernoulliCubeVector x + w) / N} ≤
      sourceLargeExposureConstant * ((N : ℝ) * p) ^ (-1 / 4 : ℝ) := by
  have hNNat : 0 < N := by omega
  have hn : 0 < (N : ℝ) := by exact_mod_cast hNNat
  have hV : 0 < Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) := by
    rw [leading_row_kernel_dimension A h hOld.ne']
    omega
  have hg : 0 < ((N - r : ℕ) : ℝ) := by
    have hNat : 0 < N - r := by omega
    exact_mod_cast hNat
  have hGap : ((N - r : ℕ) : ℝ) ≤
      9 * (Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) : ℝ) := by
    rw [leading_row_kernel_dimension A h hOld.ne']
    exact_mod_cast exposure_global_gap_le_nine_local hAmbient hrm hGuard
  have hFailure := row_addition_log_failure_probability_le_projection_small
    (bernoulliCubeLaw (Fin m) p hp) A h (fun x => bernoulliCubeVector x + w) hOld
    (δ := sourceLargeLogIncrement N (N - r : ℕ)) hn
  simp_rw [row_adjoint_bernoulli_shift] at hFailure
  exact hFailure.trans (bernoulli_projection_of_source_large_threshold p hp hpPos hHalf hNNat
    (by simpa only [Fintype.card_fin] using hAmbient) hd _ hV hg hGap hRange (rowAdjointVector w))

set_option maxHeartbeats 1500000 in
theorem bernoulli_adjoint_column_log_failure_of_source_large_threshold {N r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (h : r ≤ a) (hRow : r ≤ m) (hNext : r + 1 ≤ m)
    (hOld : 0 < leadingRowSingularProduct A h) (hAmbient : m ≤ N)
    (hd : 1 ≤ (N : ℝ) * p) (hGuard : (N - m) / 8 < m - r)
    (hRange : (N : ℝ) * ((N : ℝ) * p) ^ (-1 / 4 : ℝ) ≤ ((N - r : ℕ) : ℝ))
    (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      leadingRowLogPrefix A.conjTranspose hRow / N + sourceLargeLogIncrement N (N - r : ℕ) <
        insertedColumnLeadingLogPrefix A.conjTranspose hNext (bernoulliCubeVector x + w) / N} ≤
      sourceLargeExposureConstant * ((N : ℝ) * p) ^ (-1 / 4 : ℝ) := by
  have hNNat : 0 < N := by omega
  have hn : 0 < (N : ℝ) := by exact_mod_cast hNNat
  have hV : 0 < Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) := by
    rw [leading_row_kernel_dimension A h hOld.ne']
    omega
  have hg : 0 < ((N - r : ℕ) : ℝ) := by
    have hNat : 0 < N - r := by omega
    exact_mod_cast hNat
  have hGap : ((N - r : ℕ) : ℝ) ≤
      9 * (Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) : ℝ) := by
    rw [leading_row_kernel_dimension A h hOld.ne']
    exact_mod_cast exposure_global_gap_le_nine_local hAmbient (by omega) hGuard
  have hOldAdj : 0 < leadingRowSingularProduct A.conjTranspose hRow := by
    rwa [← leading_row_singular_product_conjTranspose A h hRow]
  have hFailure := column_addition_log_failure_probability_le_projection_small
    (bernoulliCubeLaw (Fin m) p hp) A.conjTranspose hRow h hNext
    (fun x => bernoulliCubeVector x + w) hOldAdj
    (δ := sourceLargeLogIncrement N (N - r : ℕ)) hn
  simp only [Matrix.conjTranspose_conjTranspose] at hFailure
  exact hFailure.trans (bernoulli_projection_of_source_large_threshold p hp hpPos hHalf hNNat
    (by simpa only [Fintype.card_fin] using hAmbient) hd _ hV hg hGap hRange w)

set_option maxHeartbeats 1500000 in
theorem bernoulli_row_log_failure_of_source_threshold {N r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (hrm : r < m)
    (hOld : 0 < leadingRowSingularProduct (diagonalEmbeddedShift A e z) h)
    {K β d : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbient : m ≤ N) (hAmbientLower : (N : ℝ) / 2 ≤ (m : ℝ))
    (hGuard : (N - m) / 8 < m - r) (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K N d)
    (hUnique : MatrixUniqueExpansionBudget A e β N d
      (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin))
      (sourceGraphTerminalScale N d)) (hHeavy : MatrixHeavyRowBudget A β N d)
    (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      leadingRowLogPrefix (diagonalEmbeddedShift A e z) h / N +
          sourceBernoulliLogIncrement K β N d (N - r : ℕ) <
        insertedLeadingLogPrefix (diagonalEmbeddedShift A e z) h (bernoulliCubeVector x + w) / N} ≤
      sourceExposureFailureBound d := by
  have hdPos : 0 < d := (Real.exp_pos _).trans_le hd
  unfold sourceBernoulliLogIncrement
  by_cases hRange : ((N - r : ℕ) : ℝ) ≤ (N : ℝ) * d ^ (-1 / 4 : ℝ)
  · rw [if_pos hRange]
    have hProb := bernoulli_row_log_failure_of_source_graph_threshold p hp hpPos hHalf A e z h hrm hOld
      hK hβ hβOne hd hDegree hAmbient hAmbientLower hGuard hRange hz hzUpper hColumns hUnique hHeavy w
    exact hProb.trans (le_add_of_nonneg_left
      (mul_nonneg source_large_exposure_constant_pos.le (Real.rpow_nonneg hdPos.le _)))
  · rw [if_neg hRange]
    have hdOne : 1 ≤ (N : ℝ) * p := by rw [← hDegree]; linarith [Real.add_one_le_exp (4 : ℝ)]
    have hRangeLarge : (N : ℝ) * ((N : ℝ) * p) ^ (-1 / 4 : ℝ) ≤ ((N - r : ℕ) : ℝ) := by
      rw [← hDegree]
      exact (lt_of_not_ge hRange).le
    have hProb := bernoulli_row_log_failure_of_source_large_threshold p hp hpPos hHalf
      (diagonalEmbeddedShift A e z) h hrm hOld hAmbient hdOne hGuard hRangeLarge w
    rw [← hDegree] at hProb
    exact hProb.trans (le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (by norm_num) bernoulli_scalar_small_ball_constant_pos.le)
        (Real.sqrt_nonneg _)))

set_option maxHeartbeats 1500000 in
theorem bernoulli_adjoint_column_log_failure_of_source_threshold {N r a m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (hRow : r ≤ m) (hNext : r + 1 ≤ m)
    (hOld : 0 < leadingRowSingularProduct (diagonalEmbeddedShift A e z) h)
    {K β d : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hd : Real.exp 4 ≤ d) (hDegree : d = (N : ℝ) * p)
    (hAmbient : m ≤ N) (hAmbientLower : (N : ℝ) / 2 ≤ (m : ℝ))
    (hGuard : (N - m) / 8 < m - r) (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K N d)
    (hUnique : MatrixUniqueExpansionBudget A e β N d
      (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin))
      (sourceGraphTerminalScale N d)) (hHeavy : MatrixHeavyRowBudget A β N d)
    (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x |
      leadingRowLogPrefix (diagonalEmbeddedShift A e z).conjTranspose hRow / N +
          sourceBernoulliLogIncrement K β N d (N - r : ℕ) <
        insertedColumnLeadingLogPrefix (diagonalEmbeddedShift A e z).conjTranspose hNext
          (bernoulliCubeVector x + w) / N} ≤ sourceExposureFailureBound d := by
  have hdPos : 0 < d := (Real.exp_pos _).trans_le hd
  unfold sourceBernoulliLogIncrement
  by_cases hRange : ((N - r : ℕ) : ℝ) ≤ (N : ℝ) * d ^ (-1 / 4 : ℝ)
  · rw [if_pos hRange]
    have hProb := bernoulli_adjoint_column_log_failure_of_source_graph_threshold p hp hpPos hHalf
      A e z h hRow hNext hOld hK hβ hβOne hd hDegree hAmbient hAmbientLower hGuard hRange
      hz hzUpper hColumns hUnique hHeavy w
    exact hProb.trans (le_add_of_nonneg_left
      (mul_nonneg source_large_exposure_constant_pos.le (Real.rpow_nonneg hdPos.le _)))
  · rw [if_neg hRange]
    have hdOne : 1 ≤ (N : ℝ) * p := by rw [← hDegree]; linarith [Real.add_one_le_exp (4 : ℝ)]
    have hRangeLarge : (N : ℝ) * ((N : ℝ) * p) ^ (-1 / 4 : ℝ) ≤ ((N - r : ℕ) : ℝ) := by
      rw [← hDegree]
      exact (lt_of_not_ge hRange).le
    have hProb := bernoulli_adjoint_column_log_failure_of_source_large_threshold p hp hpPos hHalf
      (diagonalEmbeddedShift A e z) h hRow hNext hOld hAmbient hdOne hGuard hRangeLarge w
    rw [← hDegree] at hProb
    exact hProb.trans (le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (by norm_num) bernoulli_scalar_small_ball_constant_pos.le)
        (Real.sqrt_nonneg _)))

end CircularLaw
