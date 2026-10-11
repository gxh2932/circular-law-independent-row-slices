import CircularLaw.SourceGraphProjectionThreshold

/-!
# The square-root degree factor in normalized graph thresholds

The paper's normalized-matrix projection threshold is sqrt(d)*eta.
Doubling the proved source-power coefficient absorbs sqrt(d), since
the source exponent dominates log(d). This checks both scalar energy
and projection-radius comparisons with that factor retained.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def sourceNormalizedGraphLogIncrement (K β n d g : ℝ) : ℝ :=
  2 * sourceGraphLogIncrement K β n d g

theorem source_graph_projection_constant_ge_one {C β : ℝ}
    (hC : 1 ≤ C) (hβ : 0 < β) (hβOne : β ≤ 1) :
    1 ≤ sourceGraphProjectionConstant C β := by
  have hLog := Real.log_nonpos hβ.le hβOne
  have hBase : 1 ≤ 22 - Real.log β := by linarith
  have hPower : 1 ≤ (22 - Real.log β) ^ 5 := one_le_pow₀ hBase
  unfold sourceGraphProjectionConstant
  nlinarith

theorem source_graph_projection_exponent_ge_log_degree {C β n d g : ℝ}
    (hC : 1 ≤ C) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hD : 1 ≤ Real.log d) (hG : 1 ≤ Real.log (n / g)) :
    Real.log d ≤ sourceGraphProjectionExponent C β n d g := by
  have hCoeff := source_graph_projection_constant_ge_one hC hβ hβOne
  have hPower : Real.log d ≤ Real.log d ^ 8 := le_self_pow₀ hD (by decide : (8 : ℕ) ≠ 0)
  have hG8 : 1 ≤ Real.log (n / g) ^ 8 := one_le_pow₀ hG
  unfold sourceGraphProjectionExponent
  exact hPower.trans ((le_mul_of_one_le_left (by positivity : 0 ≤ Real.log d ^ 8) hCoeff).trans
    (le_mul_of_one_le_right (by positivity : 0 ≤ sourceGraphProjectionConstant C β * Real.log d ^ 8) hG8))

theorem sqrt_degree_times_double_exp_le {d E : ℝ} (hd : 0 < d) (hE : Real.log d / 2 ≤ E) :
    Real.sqrt d * Real.exp (-2 * E) ≤ Real.exp (-E) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hd, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

theorem normalized_source_graph_threshold_eq {K β n d g : ℝ} (hn : 0 < n) :
    Real.sqrt d * Real.exp (-n * sourceNormalizedGraphLogIncrement K β n d g) =
      Real.sqrt d * Real.exp
        (-2 * sourceGraphProjectionExponent (graphGrowthConstant (K + 1)) β n d g) := by
  congr 2
  unfold sourceNormalizedGraphLogIncrement sourceGraphLogIncrement
  field_simp

set_option maxHeartbeats 1500000 in
theorem graph_subspace_normalized_source_threshold_comparisons {m : ℕ}
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin m))) (hV : 0 < Module.finrank ℂ V)
    {K β n d g : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hn : 4 ≤ n) (hd : Real.exp 4 ≤ d) (hAmbient : (m : ℝ) ≤ n)
    (hg : 0 < g) (hGap : g ≤ 9 * (Module.finrank ℂ V : ℝ))
    (hRange : g ≤ n * d ^ (-1 / 4 : ℝ)) :
    (Real.sqrt d * Real.exp (-n * sourceNormalizedGraphLogIncrement K β n d g)) ^ 2 <
        sourceGraphExpansion n d (subspaceSpreadCoordinateCount V) * β ^ 2 *
          graphSubspaceSpreadRadius V K β n d ^ 2 / 8 ∧
      (Real.sqrt d * Real.exp (-n * sourceNormalizedGraphLogIncrement K β n d g)) ^ 2 ≤
        (Module.finrank ℂ V : ℝ) * graphSubspaceSpreadRadius V K β n d ^ 2 / 2 := by
  have hnPos : 0 < n := by linarith
  have hdPos : 0 < d := (Real.exp_pos _).trans_le hd
  have hD : 4 ≤ Real.log d := (Real.le_log_iff_exp_le hdPos).mpr hd
  have hdFour : 4 ≤ d := by linarith [Real.add_one_le_exp (4 : ℝ)]
  obtain ⟨hG, hDG⟩ := source_projection_small_rank_log_range hnPos hd hg hRange
  have hC : 1 ≤ graphGrowthConstant (K + 1) := graph_growth_constant_ge_one (by linarith)
  have hE := source_graph_projection_exponent_ge_log_degree hC hβ hβOne (by linarith : 1 ≤ Real.log d) hG
  have hThreshold : Real.sqrt d * Real.exp (-n * sourceNormalizedGraphLogIncrement K β n d g) ≤
      Real.exp (-sourceGraphProjectionExponent (graphGrowthConstant (K + 1)) β n d g) := by
    rw [normalized_source_graph_threshold_eq hnPos]
    exact sqrt_degree_times_double_exp_le hdPos (by linarith)
  exact graph_subspace_source_threshold_comparisons V hV hK hβ hβOne hn hdFour hAmbient
    hg hGap (by linarith : 1 ≤ Real.log d) hG hDG (by positivity) hThreshold

set_option maxHeartbeats 1500000 in
theorem leading_kernel_normalized_source_threshold_comparisons {N r a m : ℕ}
    (A : Matrix (Fin a) (Fin m) ℂ) (h : r ≤ a) (hrm : r < m)
    (hProd : leadingRowSingularProduct A h ≠ 0)
    {K β d : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hN : 4 ≤ (N : ℝ)) (hd : Real.exp 4 ≤ d) (hAmbient : m ≤ N)
    (hGuard : (N - m) / 8 < m - r)
    (hRange : ((N - r : ℕ) : ℝ) ≤ (N : ℝ) * d ^ (-1 / 4 : ℝ)) :
    (Real.sqrt d * Real.exp (-(N : ℝ) * sourceNormalizedGraphLogIncrement K β N d (N - r : ℕ))) ^ 2 <
        sourceGraphExpansion N d (subspaceSpreadCoordinateCount
          (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin)) * β ^ 2 *
          graphSubspaceSpreadRadius (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin)
            K β N d ^ 2 / 8 ∧
      (Real.sqrt d * Real.exp (-(N : ℝ) * sourceNormalizedGraphLogIncrement K β N d (N - r : ℕ))) ^ 2 ≤
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
  exact graph_subspace_normalized_source_threshold_comparisons _ hV hK hβ hβOne hN hd
    (by exact_mod_cast hAmbient) hg hGap hRange

end CircularLaw
