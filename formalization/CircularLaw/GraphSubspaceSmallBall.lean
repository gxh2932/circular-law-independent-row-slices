import CircularLaw.GraphNearKernelIteration
import CircularLaw.BernoulliSubspaceSmallBall

/-!
# Graph spreading gives an actual Bernoulli projection bound

The initial spread basis is proved to exist. If its coordinate count is
below the terminal scale, the checked integer graph iteration spreads
each vector further. Otherwise its original spread already suffices at
the smaller graph radius. The actual Bernoulli projection probability
then uses that coordinate set.
Near-kernel energy and projection-radius comparisons remain explicit.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def graphSubspaceSpreadRadius {m : ℕ} (V : Submodule ℂ (EuclideanSpace ℂ (Fin m)))
    (K β n d : ℝ) : ℝ := sourceGraphIterationRadius (graphGrowthConstant (K + 1)) β n d
      (subspaceSpreadCoordinateCount V) (subspaceSpreadRadius V)

theorem source_graph_terminal_probability_factor {n d p C : ℝ}
    (hn : 0 < n) (hp : 0 < p) (hd : Real.exp (Real.exp 1) ≤ d)
    (hDegree : d = n * p) (hC : 0 ≤ C) :
    2 * C / Real.sqrt ((Nat.ceil (sourceGraphTerminalScale n d) : ℝ) * p) ≤
      4 * C / Real.sqrt (Real.log (Real.log d)) := by
  have hdp : 0 < d := (Real.exp_pos _).trans_le hd
  have hLogD : Real.exp 1 ≤ Real.log d := (Real.le_log_iff_exp_le hdp).mpr hd
  have hLogDp : 0 < Real.log d := (Real.exp_pos _).trans_le hLogD
  have hLogLog : 1 ≤ Real.log (Real.log d) := (Real.le_log_iff_exp_le hLogDp).mpr hLogD
  have hLPos : 0 < Real.log (Real.log d) := by linarith
  have hIdentity : sourceGraphTerminalScale n d * p = Real.log (Real.log d) / 2 := by
    unfold sourceGraphTerminalScale
    rw [hDegree]
    field_simp
  have hLower : Real.log (Real.log d) / 2 ≤
      (Nat.ceil (sourceGraphTerminalScale n d) : ℝ) * p := by
    rw [← hIdentity]
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) hp.le
  have hProdPos : 0 < (Nat.ceil (sourceGraphTerminalScale n d) : ℝ) * p := by linarith
  have hRoot : Real.sqrt (Real.log (Real.log d)) ≤
      2 * Real.sqrt ((Nat.ceil (sourceGraphTerminalScale n d) : ℝ) * p) := by
    nlinarith [Real.sq_sqrt hLPos.le, Real.sq_sqrt hProdPos.le,
      Real.sqrt_nonneg (Real.log (Real.log d)),
      Real.sqrt_nonneg ((Nat.ceil (sourceGraphTerminalScale n d) : ℝ) * p)]
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hProdPos) (Real.sqrt_pos.mpr hLPos)).mpr
  have h := mul_le_mul_of_nonneg_left hRoot (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
  nlinarith

theorem graph_subspace_spread_radius_pos {m : ℕ}
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin m))) (hV : 0 < Module.finrank ℂ V)
    {K β n d : ℝ} (hβ : 0 < β) (hn : 0 < n) (hd : 0 < d) :
    0 < graphSubspaceSpreadRadius V K β n d := by
  have hInitial := subspace_spread_radius_pos V hV
  have hk := subspace_spread_coordinate_count_pos V hV
  have hkReal : 0 < (subspaceSpreadCoordinateCount V : ℝ) := by exact_mod_cast hk
  unfold graphSubspaceSpreadRadius sourceGraphIterationRadius
  positivity

theorem ordered_norm_at_ge_of_coordinate_spread {m k : ℕ}
    (v : EuclideanSpace ℂ (Fin m)) (hk : 0 < k) (hkm : k ≤ m) {a : ℝ}
    (hCount : k ≤ (coordinateSpreadSet v a).card) :
    a ≤ orderedNormAt (fun j => v j) k := by
  classical
  by_contra hNot
  have hSmall : orderedNormAt (fun j => v j) k < a := lt_of_not_ge hNot
  have hSubset : coordinateSpreadSet v a ⊆ orderedPrefix (fun j => v j) (k - 1) := by
    intro j hj
    by_contra hOutside
    have hTail := norm_le_ordered_norm_at_outside_predecessor (fun j => v j) hk hkm j hOutside
    have hLarge := (coordinate_spread_set_mem v a j).mp hj
    linarith
  have hCard := Finset.card_le_card hSubset
  rw [orderedPrefix_card _ (by omega : k - 1 ≤ m)] at hCard
  omega

theorem subspace_spread_coordinate_count_le_ambient {ι : Type*} [Fintype ι]
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) :
    subspaceSpreadCoordinateCount V ≤ Fintype.card ι := by
  unfold subspaceSpreadCoordinateCount
  apply Nat.ceil_le.mpr
  have hLe := V.finrank_le
  rw [finrank_euclideanSpace] at hLe
  have hCast : (Module.finrank ℂ V : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hLe
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4096)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]

theorem graph_subspace_spread_radius_le_initial {m : ℕ}
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin m))) (hV : 0 < Module.finrank ℂ V)
    {K β n d : ℝ} (hβ : 0 < β) (hβOne : β ≤ 1) (hn : 0 < n) (hd : 1 ≤ d)
    (hAmbientUpper : (m : ℝ) ≤ n) :
    graphSubspaceSpreadRadius V K β n d ≤ subspaceSpreadRadius V := by
  have hk := subspace_spread_coordinate_count_pos V hV
  have hkReal : 0 < (subspaceSpreadCoordinateCount V : ℝ) := by exact_mod_cast hk
  have hkm : subspaceSpreadCoordinateCount V ≤ m := by
    simpa only [Fintype.card_fin] using subspace_spread_coordinate_count_le_ambient V
  have hkn : (subspaceSpreadCoordinateCount V : ℝ) ≤ n :=
    (by exact_mod_cast hkm : (subspaceSpreadCoordinateCount V : ℝ) ≤ m).trans hAmbientUpper
  obtain ⟨hδPos, hδOne⟩ := source_graph_gap_ratio_range hβ hβOne hn hd hkReal hkn
  unfold graphSubspaceSpreadRadius sourceGraphIterationRadius
  exact mul_le_of_le_one_right (subspace_spread_radius_pos V hV).le
    (pow_le_one₀ hδPos.le hδOne)

set_option maxHeartbeats 1500000 in
theorem exists_graph_spread_subspace_basis {ρ : Type*} [Fintype ρ] {m : ℕ}
    (A : Matrix ρ (Fin m) ℂ) (e : ρ ↪ Fin m) (z : ℂ)
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin m))) (hV : 0 < Module.finrank ℂ V)
    {K β n d u s : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hn : 0 < n) (hd : 4 ≤ d) (hAmbientUpper : (m : ℝ) ≤ n)
    (hu : 0 < u) (huN : u ≤ n) (hLog : 1 ≤ Real.log (n / u)) (hAmbient : 2 * u ≤ (m : ℝ))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K n d)
    (hUnique : MatrixUniqueExpansionBudget A e β n d (subspaceSpreadCoordinateCount V) u)
    (hHeavy : MatrixHeavyRowBudget A β n d)
    (hNear : ∀ v : V, ‖(diagonalEmbeddedShift A e z).toEuclideanLin (v : EuclideanSpace ℂ (Fin m))‖ ^ 2 ≤
      s ^ 2 * ‖v‖ ^ 2)
    (hSmall : s ^ 2 < sourceGraphExpansion n d (subspaceSpreadCoordinateCount V) * β ^ 2 *
      graphSubspaceSpreadRadius V K β n d ^ 2 / 8) :
    ∃ B : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V, ∀ j,
      Nat.ceil u ≤ (coordinateSpreadSet (B j : EuclideanSpace ℂ (Fin m))
        (graphSubspaceSpreadRadius V K β n d)).card := by
  obtain ⟨B, hB⟩ := exists_subspace_spread_basis V hV
  have hk := subspace_spread_coordinate_count_pos V hV
  have hkm : subspaceSpreadCoordinateCount V ≤ m := by
    simpa only [Fintype.card_fin] using subspace_spread_coordinate_count_le_ambient V
  refine ⟨B, fun j => ?_⟩
  by_cases hku : (subspaceSpreadCoordinateCount V : ℝ) ≤ u
  · have hInitial := ordered_norm_at_ge_of_coordinate_spread
      (B j : EuclideanSpace ℂ (Fin m)) hk hkm (hB j).2
    have hImage := hNear (B j)
    rw [B.norm_eq_one, one_pow, mul_one] at hImage
    have hSmallVector := hImage.trans_lt hSmall
    have hSpread := source_graph_near_kernel_iterated_spread A e z
      (B j : EuclideanSpace ℂ (Fin m)) hK hβ hβOne hn hd hk hku hu huN hLog hAmbient
      hz hzUpper hColumns hUnique hHeavy (subspace_spread_radius_pos V hV) hInitial hSmallVector
    exact Nat.ceil_le.mpr hSpread.le
  · have hRadius := graph_subspace_spread_radius_le_initial (K := K) V hV hβ hβOne hn
      (by linarith : 1 ≤ d) hAmbientUpper
    have hSubset : coordinateSpreadSet (B j : EuclideanSpace ℂ (Fin m)) (subspaceSpreadRadius V) ⊆
        coordinateSpreadSet (B j : EuclideanSpace ℂ (Fin m)) (graphSubspaceSpreadRadius V K β n d) := by
      intro i hi
      exact (coordinate_spread_set_mem _ _ i).mpr (hRadius.trans ((coordinate_spread_set_mem _ _ i).mp hi))
    have hCount := (hB j).2.trans (Finset.card_le_card hSubset)
    have hCountReal : (subspaceSpreadCoordinateCount V : ℝ) ≤
        ((coordinateSpreadSet (B j : EuclideanSpace ℂ (Fin m)) (graphSubspaceSpreadRadius V K β n d)).card : ℝ) :=
      by exact_mod_cast hCount
    exact Nat.ceil_le.mpr ((lt_of_not_ge hku).trans_le hCountReal).le

set_option maxHeartbeats 1500000 in
theorem bernoulli_projection_norm_small_ball_of_graph {ρ : Type*} [Fintype ρ] {m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix ρ (Fin m) ℂ) (e : ρ ↪ Fin m) (z : ℂ)
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin m))) (hV : 0 < Module.finrank ℂ V)
    {K β n d u s L : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hn : 0 < n) (hd : 4 ≤ d) (hAmbientUpper : (m : ℝ) ≤ n)
    (hu : 0 < u) (huN : u ≤ n) (hLog : 1 ≤ Real.log (n / u)) (hAmbient : 2 * u ≤ (m : ℝ))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K n d)
    (hUnique : MatrixUniqueExpansionBudget A e β n d (subspaceSpreadCoordinateCount V) u)
    (hHeavy : MatrixHeavyRowBudget A β n d)
    (hNear : ∀ v : V, ‖(diagonalEmbeddedShift A e z).toEuclideanLin (v : EuclideanSpace ℂ (Fin m))‖ ^ 2 ≤
      s ^ 2 * ‖v‖ ^ 2)
    (hSmall : s ^ 2 < sourceGraphExpansion n d (subspaceSpreadCoordinateCount V) * β ^ 2 *
      graphSubspaceSpreadRadius V K β n d ^ 2 / 8)
    (hL : 0 ≤ L) (hRadius : L ^ 2 ≤ (Module.finrank ℂ V : ℝ) *
      graphSubspaceSpreadRadius V K β n d ^ 2 / 2) (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x | ‖V.starProjection (bernoulliCubeVector x + w)‖ < L} ≤
      2 * bernoulliScalarSmallBallConstant / Real.sqrt ((Nat.ceil u : ℝ) * p) := by
  classical
  obtain ⟨B, hB⟩ := exists_graph_spread_subspace_basis A e z V hV hK hβ hβOne hn hd hAmbientUpper
    hu huN hLog hAmbient hz hzUpper hColumns hUnique hHeavy hNear hSmall
  have hR : 0 < graphSubspaceSpreadRadius V K β n d :=
    graph_subspace_spread_radius_pos V hV hβ hn (by linarith : 0 < d)
  have hCeil : 0 < Nat.ceil u := Nat.ceil_pos.mpr hu
  have hCard : ∀ j, (coordinateSpreadSet (B j : EuclideanSpace ℂ (Fin m))
      (graphSubspaceSpreadRadius V K β n d)).Nonempty := by
    intro j
    exact Finset.card_pos.mp (hCeil.trans_le (hB j))
  have hProb := bernoulli_projection_small_ball_of_uniform_spread p hp hpPos hHalf V B
    (by simpa using hV) w
    (fun j => coordinateSpreadSet (B j : EuclideanSpace ℂ (Fin m)) (graphSubspaceSpreadRadius V K β n d))
    hCard hCeil hB hR (fun j i hi => (coordinate_spread_set_mem _ _ i).mp hi)
    (by linarith : graphSubspaceSpreadRadius V K β n d / 2 ≤ graphSubspaceSpreadRadius V K β n d)
  simp only [div_self hR.ne', mul_one, Fintype.card_fin] at hProb
  have hContainment : {x | ‖V.starProjection (bernoulliCubeVector x + w)‖ < L} ⊆
      {x | ‖V.starProjection (bernoulliCubeVector x + w)‖ ^ 2 ≤
        (Module.finrank ℂ V : ℝ) * graphSubspaceSpreadRadius V K β n d ^ 2 / 2} := by
    intro x hx
    exact ((sq_le_sq₀ (norm_nonneg _) hL).mpr hx.le).trans hRadius
  exact (measureReal_mono (h₂ := by finiteness) hContainment).trans hProb

set_option maxHeartbeats 1500000 in
theorem bernoulli_projection_norm_small_ball_of_terminal_graph {ρ : Type*} [Fintype ρ] {m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix ρ (Fin m) ℂ) (e : ρ ↪ Fin m) (z : ℂ)
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin m))) (hV : 0 < Module.finrank ℂ V)
    {K β n d s L : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1)
    (hn : 0 < n) (hd : Real.exp (Real.exp 1) ≤ d) (hDegree : d = n * p)
    (hAmbientUpper : (m : ℝ) ≤ n)
    (hAmbient : n / 2 ≤ (m : ℝ)) (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K n d)
    (hUnique : MatrixUniqueExpansionBudget A e β n d (subspaceSpreadCoordinateCount V)
      (sourceGraphTerminalScale n d)) (hHeavy : MatrixHeavyRowBudget A β n d)
    (hNear : ∀ v : V, ‖(diagonalEmbeddedShift A e z).toEuclideanLin (v : EuclideanSpace ℂ (Fin m))‖ ^ 2 ≤
      s ^ 2 * ‖v‖ ^ 2)
    (hSmall : s ^ 2 < sourceGraphExpansion n d (subspaceSpreadCoordinateCount V) * β ^ 2 *
      graphSubspaceSpreadRadius V K β n d ^ 2 / 8)
    (hL : 0 ≤ L) (hRadius : L ^ 2 ≤ (Module.finrank ℂ V : ℝ) *
      graphSubspaceSpreadRadius V K β n d ^ 2 / 2) (w : EuclideanSpace ℂ (Fin m)) :
    (bernoulliCubeLaw (Fin m) p hp).real {x | ‖V.starProjection (bernoulliCubeVector x + w)‖ < L} ≤
      4 * bernoulliScalarSmallBallConstant / Real.sqrt (Real.log (Real.log d)) := by
  have hE : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hExp : 4 ≤ Real.exp (1 + 1) := by rw [Real.exp_add]; nlinarith
  have hdFour : 4 ≤ d := hExp.trans
    ((Real.exp_le_exp.mpr (by linarith : (1 : ℝ) + 1 ≤ Real.exp 1)).trans hd)
  obtain ⟨hu, hUpper, hLog⟩ := source_graph_terminal_range hn hd
  have hProb := bernoulli_projection_norm_small_ball_of_graph p hp hpPos hHalf A e z V hV
    hK hβ hβOne hn hdFour hAmbientUpper hu (by linarith : sourceGraphTerminalScale n d ≤ n) hLog
    (by linarith : 2 * sourceGraphTerminalScale n d ≤ (m : ℝ)) hz hzUpper
    hColumns hUnique hHeavy hNear hSmall hL hRadius w
  exact hProb.trans (source_graph_terminal_probability_factor hn hpPos hd hDegree
    bernoulli_scalar_small_ball_constant_pos.le)

end CircularLaw
