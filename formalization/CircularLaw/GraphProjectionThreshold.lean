import CircularLaw.GraphLeadingKernel

/-!
# A sufficient scalar threshold for graph projection and image energy

The seed count k is at least h/4096. A threshold no larger than
beta*sqrt(h)*R/(128*(1+log(n/k))) satisfies both comparisons required
by the graph exposure estimate. The exact normalized expression cancels
the square roots of the subspace dimension.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def graphProjectionThreshold (h R β L : ℝ) : ℝ :=
  β * Real.sqrt h * R / (128 * (1 + L))

def graphProjectionLogCost (C β n d : ℝ) (k : ℕ) (h m : ℝ) : ℝ :=
  Real.log (8192 * m / h) + Real.log (1 + Real.log (n / k)) - Real.log β +
    7 * (sourceGraphIterationSteps C n k : ℝ) * Real.log (d * n / (β * k))

theorem graph_projection_threshold_pos {h R β L : ℝ}
    (hh : 0 < h) (hR : 0 < R) (hβ : 0 < β) (hL : 0 ≤ L) :
    0 < graphProjectionThreshold h R β L := by
  unfold graphProjectionThreshold
  positivity

theorem graph_projection_threshold_sq {h R β L : ℝ} (hh : 0 ≤ h) :
    graphProjectionThreshold h R β L ^ 2 =
      h / (128 ^ 2 * (1 + L) ^ 2) * (β ^ 2 * R ^ 2) := by
  unfold graphProjectionThreshold
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hh, mul_pow]
  ring

set_option maxHeartbeats 1000000 in
theorem graph_projection_threshold_comparisons {h k R β L d η : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ 4096 * k)
    (hR : 0 < R) (hβ : 0 < β) (hβOne : β ≤ 1) (hL : 0 < L) (hd : 4 ≤ d)
    (hη : 0 ≤ η) (hThreshold : η ≤ graphProjectionThreshold h R β L) :
    η ^ 2 < (d * k / L ^ 2) * β ^ 2 * R ^ 2 / 8 ∧
      η ^ 2 ≤ h * R ^ 2 / 2 := by
  have hTPos := graph_projection_threshold_pos hh hR hβ hL.le
  have hEtaSq := (sq_le_sq₀ hη hTPos.le).mpr hThreshold
  have hLogs : L ^ 2 ≤ (1 + L) ^ 2 :=
    (sq_le_sq₀ hL.le (by linarith : 0 ≤ 1 + L)).mpr (by linarith)
  have hCoeff : h / (128 ^ 2 * (1 + L) ^ 2) ≤ d * k / (16 * L ^ 2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 128 ^ 2 * (1 + L) ^ 2)
      (by positivity : 0 < 16 * L ^ 2)).mpr
    calc
      h * (16 * L ^ 2) ≤ (4096 * k) * (16 * L ^ 2) :=
        mul_le_mul_of_nonneg_right hhk (by positivity)
      _ = (4 * k) * (128 ^ 2 * L ^ 2) := by ring
      _ ≤ (d * k) * (128 ^ 2 * (1 + L) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hd hk.le)
          (mul_le_mul_of_nonneg_left hLogs (by norm_num)) (by positivity) (by positivity)
  have hEnergyHalf : graphProjectionThreshold h R β L ^ 2 ≤
      ((d * k / L ^ 2) * β ^ 2 * R ^ 2 / 8) / 2 := by
    rw [graph_projection_threshold_sq hh.le]
    calc
      _ ≤ (d * k / (16 * L ^ 2)) * (β ^ 2 * R ^ 2) :=
        mul_le_mul_of_nonneg_right hCoeff (by positivity)
      _ = _ := by ring
  have hEnergyPos : 0 < (d * k / L ^ 2) * β ^ 2 * R ^ 2 / 8 := by
    have hdp : 0 < d := by linarith
    positivity
  have hDen : 2 ≤ 128 ^ 2 * (1 + L) ^ 2 := by
    have hOne : 1 ≤ (1 + L) ^ 2 := by nlinarith [sq_nonneg L]
    nlinarith
  have hCoeffRadius : h / (128 ^ 2 * (1 + L) ^ 2) ≤ h / 2 :=
    div_le_div_of_nonneg_left hh.le (by norm_num) hDen
  have hBeta : β ^ 2 ≤ 1 := pow_le_one₀ hβ.le hβOne
  have hRadius : graphProjectionThreshold h R β L ^ 2 ≤ h * R ^ 2 / 2 := by
    rw [graph_projection_threshold_sq hh.le]
    calc
      _ ≤ (h / 2) * (1 * R ^ 2) := mul_le_mul hCoeffRadius
        (mul_le_mul_of_nonneg_right hBeta (sq_nonneg R)) (by positivity) (by positivity)
      _ = _ := by ring
  exact ⟨by linarith, hEtaSq.trans hRadius⟩

theorem graph_projection_normalized_eq_exp_cost {C β n d h m : ℝ} {k : ℕ}
    (hβ : 0 < β) (hn : 0 < n) (hd : 0 < d) (hk : 0 < k)
    (hh : 0 < h) (hm : 0 < m) (hL : 0 ≤ Real.log (n / k)) :
    β * h / (8192 * m * (1 + Real.log (n / k))) *
      ((β * k / (d * n)) ^ 7) ^ sourceGraphIterationSteps C n k =
      Real.exp (-graphProjectionLogCost C β n d k h m) := by
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hLp : 0 < 1 + Real.log (n / k) := by linarith
  have hRatio : 0 < β * k / (d * n) := by positivity
  have hValue : 0 < β * h / (8192 * m * (1 + Real.log (n / k))) *
      ((β * k / (d * n)) ^ 7) ^ sourceGraphIterationSteps C n k := by positivity
  have hLogRatio : Real.log (β * k / (d * n)) = -Real.log (d * n / (β * k)) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity)]
    ring
  have hLog : Real.log (β * h / (8192 * m * (1 + Real.log (n / k))) *
      ((β * k / (d * n)) ^ 7) ^ sourceGraphIterationSteps C n k) =
      -graphProjectionLogCost C β n d k h m := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity),
      Real.log_mul hβ.ne' hh.ne',
      Real.log_mul (by positivity) hLp.ne', Real.log_mul (by norm_num) hm.ne',
      Real.log_pow, Real.log_pow, hLogRatio]
    unfold graphProjectionLogCost
    rw [Real.log_div (by positivity) hh.ne', Real.log_mul (by norm_num) hm.ne']
    ring
  rw [← hLog, Real.exp_log hValue]

theorem graph_subspace_projection_threshold_eq_exp_cost {m : ℕ}
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin m))) (hV : 0 < Module.finrank ℂ V)
    {K β n d : ℝ} (hβ : 0 < β) (hn : 0 < n) (hd : 0 < d)
    (hL : 0 ≤ Real.log (n / subspaceSpreadCoordinateCount V)) :
    graphProjectionThreshold (Module.finrank ℂ V)
      (graphSubspaceSpreadRadius V K β n d) β
      (Real.log (n / subspaceSpreadCoordinateCount V)) =
      Real.exp (-graphProjectionLogCost (graphGrowthConstant (K + 1)) β n d
        (subspaceSpreadCoordinateCount V) (Module.finrank ℂ V) m) := by
  have hh : 0 < (Module.finrank ℂ V : ℝ) := by exact_mod_cast hV
  have hmNat : 0 < m := hV.trans_le (by simpa only [finrank_euclideanSpace, Fintype.card_fin] using V.finrank_le)
  have hm : 0 < (m : ℝ) := by exact_mod_cast hmNat
  rw [← graph_projection_normalized_eq_exp_cost hβ hn hd
    (subspace_spread_coordinate_count_pos V hV) hh hm hL]
  unfold graphProjectionThreshold graphSubspaceSpreadRadius sourceGraphIterationRadius subspaceSpreadRadius
  simp only [Fintype.card_fin]
  have hRoot := Real.sq_sqrt hh.le
  field_simp
  rw [hRoot]
  ring

end CircularLaw
