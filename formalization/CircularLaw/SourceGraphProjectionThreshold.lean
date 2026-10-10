import CircularLaw.GraphProjectionCost
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Source-power thresholds in the exposure range

The integer moving barrier controls the global remaining size by nine
times the local kernel dimension. In the small-dimension source range,
the source degree and remaining-size eighth powers dominate the exact
graph projection cost. Both required threshold comparisons are proved.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def sourceGraphLogIncrement (K β n d g : ℝ) : ℝ :=
  sourceGraphProjectionExponent (graphGrowthConstant (K + 1)) β n d g / n

theorem exposure_global_gap_le_nine_local {N m r : ℕ}
    (hm : m ≤ N) (hr : r < m) (hGuard : (N - m) / 8 < m - r) :
    N - r ≤ 9 * (m - r) := by
  omega

theorem source_projection_small_rank_log_range {n d g : ℝ}
    (hn : 0 < n) (hd : Real.exp 4 ≤ d) (hg : 0 < g)
    (hRange : g ≤ n * d ^ (-1 / 4 : ℝ)) :
    1 ≤ Real.log (n / g) ∧ Real.log d ≤ 4 * Real.log (n / g) := by
  have hdp : 0 < d := (Real.exp_pos _).trans_le hd
  have hD : 4 ≤ Real.log d := (Real.le_log_iff_exp_le hdp).mpr hd
  have hPow : 0 < d ^ (-1 / 4 : ℝ) := Real.rpow_pos_of_pos hdp _
  have hLog := Real.log_le_log hg hRange
  rw [Real.log_mul hn.ne' hPow.ne', Real.log_rpow hdp] at hLog
  rw [Real.log_div hn.ne' hg.ne']
  constructor <;> linarith

theorem source_graph_log_increment_threshold_eq {K β n d g : ℝ} (hn : 0 < n) :
    Real.exp (-n * sourceGraphLogIncrement K β n d g) =
      Real.exp (-sourceGraphProjectionExponent (graphGrowthConstant (K + 1)) β n d g) := by
  congr 1
  unfold sourceGraphLogIncrement
  field_simp

set_option maxHeartbeats 1500000 in
theorem graph_subspace_source_threshold_comparisons {m : ℕ}
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin m))) (hV : 0 < Module.finrank ℂ V)
    {K β n d g η : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hn : 4 ≤ n) (hd : 4 ≤ d) (hAmbient : (m : ℝ) ≤ n)
    (hg : 0 < g) (hGap : g ≤ 9 * (Module.finrank ℂ V : ℝ))
    (hD : 1 ≤ Real.log d) (hG : 1 ≤ Real.log (n / g))
    (hDG : Real.log d ≤ 4 * Real.log (n / g))
    (hη : 0 ≤ η) (hThreshold : η ≤ Real.exp
      (-sourceGraphProjectionExponent (graphGrowthConstant (K + 1)) β n d g)) :
    η ^ 2 < sourceGraphExpansion n d (subspaceSpreadCoordinateCount V) * β ^ 2 *
        graphSubspaceSpreadRadius V K β n d ^ 2 / 8 ∧
      η ^ 2 ≤ (Module.finrank ℂ V : ℝ) * graphSubspaceSpreadRadius V K β n d ^ 2 / 2 := by
  have hnPos : 0 < n := by linarith
  have hdPos : 0 < d := by linarith
  have hh : 0 < (Module.finrank ℂ V : ℝ) := by exact_mod_cast hV
  have hDimNat : Module.finrank ℂ V ≤ m := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using V.finrank_le
  have hDim : (Module.finrank ℂ V : ℝ) ≤ m := by exact_mod_cast hDimNat
  have hm : 0 < (m : ℝ) := hh.trans_le hDim
  have hk := subspace_spread_coordinate_count_pos V hV
  have hkReal : 0 < (subspaceSpreadCoordinateCount V : ℝ) := by exact_mod_cast hk
  have hKH : (subspaceSpreadCoordinateCount V : ℝ) ≤ (Module.finrank ℂ V : ℝ) := by
    exact_mod_cast subspace_spread_coordinate_count_le_dimension V
  have hSeed := subspace_spread_coordinate_count_lower V
  have hHK : (Module.finrank ℂ V : ℝ) ≤ 4096 * (subspaceSpreadCoordinateCount V : ℝ) := by
    linarith
  have hLog := graph_subspace_seed_log_pos V hV hn hAmbient
  have hC : 1 ≤ graphGrowthConstant (K + 1) := graph_growth_constant_ge_one (by linarith)
  have hCost := graph_projection_log_cost_le_source_power hC hβ hβOne hnPos hdPos
    hk hh hm hKH hDim hAmbient hSeed hg hGap hD hG hDG
  have hBound : η ≤ graphProjectionThreshold (Module.finrank ℂ V)
      (graphSubspaceSpreadRadius V K β n d) β (Real.log (n / subspaceSpreadCoordinateCount V)) := by
    rw [graph_subspace_projection_threshold_eq_exp_cost V hV hβ hnPos hdPos hLog.le]
    exact hThreshold.trans (Real.exp_le_exp.mpr (neg_le_neg hCost))
  have hR : 0 < graphSubspaceSpreadRadius V K β n d :=
    graph_subspace_spread_radius_pos V hV hβ hnPos hdPos
  simpa only [sourceGraphExpansion] using
    graph_projection_threshold_comparisons hh hkReal hHK hR hβ hβOne hLog hd hη hBound

set_option maxHeartbeats 1500000 in
theorem graph_subspace_source_threshold_at_small_rank {m : ℕ}
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin m))) (hV : 0 < Module.finrank ℂ V)
    {K β n d g : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hn : 4 ≤ n) (hd : Real.exp 4 ≤ d) (hAmbient : (m : ℝ) ≤ n)
    (hg : 0 < g) (hGap : g ≤ 9 * (Module.finrank ℂ V : ℝ))
    (hRange : g ≤ n * d ^ (-1 / 4 : ℝ)) :
    Real.exp (-n * sourceGraphLogIncrement K β n d g) ^ 2 <
        sourceGraphExpansion n d (subspaceSpreadCoordinateCount V) * β ^ 2 *
          graphSubspaceSpreadRadius V K β n d ^ 2 / 8 ∧
      Real.exp (-n * sourceGraphLogIncrement K β n d g) ^ 2 ≤
        (Module.finrank ℂ V : ℝ) * graphSubspaceSpreadRadius V K β n d ^ 2 / 2 := by
  have hnPos : 0 < n := by linarith
  have hdPos : 0 < d := (Real.exp_pos _).trans_le hd
  have hD : 4 ≤ Real.log d := (Real.le_log_iff_exp_le hdPos).mpr hd
  have hdFour : 4 ≤ d := by linarith [Real.add_one_le_exp (4 : ℝ)]
  obtain ⟨hG, hDG⟩ := source_projection_small_rank_log_range hnPos hd hg hRange
  apply graph_subspace_source_threshold_comparisons V hV hK hβ hβOne hn hdFour hAmbient
    hg hGap (by linarith : 1 ≤ Real.log d) hG hDG (Real.exp_pos _).le
  rw [source_graph_log_increment_threshold_eq hnPos]

set_option maxHeartbeats 1500000 in
theorem leading_kernel_source_threshold_comparisons {N r a m : ℕ}
    (A : Matrix (Fin a) (Fin m) ℂ) (h : r ≤ a) (hrm : r < m)
    (hProd : leadingRowSingularProduct A h ≠ 0)
    {K β d : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hN : 4 ≤ (N : ℝ)) (hd : Real.exp 4 ≤ d) (hAmbient : m ≤ N)
    (hGuard : (N - m) / 8 < m - r)
    (hRange : ((N - r : ℕ) : ℝ) ≤ (N : ℝ) * d ^ (-1 / 4 : ℝ)) :
    Real.exp (-(N : ℝ) * sourceGraphLogIncrement K β N d (N - r : ℕ)) ^ 2 <
        sourceGraphExpansion N d (subspaceSpreadCoordinateCount
          (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin)) * β ^ 2 *
          graphSubspaceSpreadRadius (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin)
            K β N d ^ 2 / 8 ∧
      Real.exp (-(N : ℝ) * sourceGraphLogIncrement K β N d (N - r : ℕ)) ^ 2 ≤
        (Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) : ℝ) *
          graphSubspaceSpreadRadius (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin)
            K β N d ^ 2 / 2 := by
  have hV : 0 < Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) := by
    rw [leading_row_kernel_dimension A h hProd]
    omega
  have hg : 0 < ((N - r : ℕ) : ℝ) := by
    have hNat : 0 < N - r := by omega
    exact_mod_cast hNat
  have hGap : ((N - r : ℕ) : ℝ) ≤
      9 * (Module.finrank ℂ (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) : ℝ) := by
    rw [leading_row_kernel_dimension A h hProd]
    exact_mod_cast exposure_global_gap_le_nine_local hAmbient hrm hGuard
  exact graph_subspace_source_threshold_at_small_rank _ hV hK hβ hβOne hN hd
    (by exact_mod_cast hAmbient) hg hGap hRange

end CircularLaw
