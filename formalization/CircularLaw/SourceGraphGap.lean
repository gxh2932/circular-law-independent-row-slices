import CircularLaw.GraphGrowthBudget
import CircularLaw.GraphNearKernelGap

/-!
# Coordinate-gap amplification from the source graph budgets

The actual growth function supplies the middle-coordinate bound from
the uniform column-degree budget. Expansion and heavy-row conditions
are imposed on actual finite supports, uniformly over the relevant sets.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def MatrixUniqueExpansionBudget {ρ ι : Type*} [Fintype ρ]
    (A : Matrix ρ ι ℂ) (e : ρ ↪ ι) (β n d k u : ℝ) : Prop :=
  ∀ S : Finset ι, k ≤ S.card → (S.card : ℝ) ≤ u →
    sourceGraphExpansion n d S.card ≤ ((matrixUniqueNeighbourhood A e β S).card : ℝ)

def MatrixHeavyRowBudget {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (A : Matrix ρ ι ℂ) (β n d : ℝ) : Prop :=
  ∀ ell : ℕ, 0 < ell → 1 ≤ Real.log (n / ell) →
    ((matrixHeavyRows A ((d * n / (β * ell)) ^ 5 / β)).card : ℝ) ≤
      sourceGraphExpansion n d ell / 4

theorem source_graph_middle_support_budget {ρ ι : Type*} [Fintype ρ]
    (A : Matrix ρ ι ℂ) {K n d x : ℝ} (hK : 0 ≤ K) (hn : 0 < n)
    (hd : 1 ≤ d) (hx : 0 < x) (hLog : 1 ≤ Real.log (n / x))
    (hA : MatrixColumnDegreeBudget A K n d) (T : Finset ι)
    (hCard : T.card ≤ sourceGraphGrowth (graphGrowthConstant (K + 1)) n d x - 1) :
    ((∑ j ∈ T, ((matrixColumnSupport A j).card + 1) : ℕ) : ℝ) ≤
      sourceGraphExpansion n d x / 4 := by
  classical
  have hKp : 0 ≤ K + 1 := by linarith
  have hCp : 0 < graphGrowthConstant (K + 1) :=
    lt_of_lt_of_le (by norm_num) (graph_growth_constant_ge_one hKp)
  have hdp : 0 < d := by linarith
  have hB : 0 < sourceGraphExpansion n d x := by
    have hLp : 0 < Real.log (n / x) := by linarith
    unfold sourceGraphExpansion
    positivity
  by_cases hEmpty : T.card = 0
  · have hT : T = ∅ := Finset.card_eq_zero.mp hEmpty
    simp only [hT, Finset.sum_empty, Nat.cast_zero]
    positivity
  let s : ℝ := T.card
  have hs : 0 < s := by dsimp [s]; exact_mod_cast Nat.pos_of_ne_zero hEmpty
  have hsBase : s ≤ sourceGraphGrowthBase (graphGrowthConstant (K + 1)) n d x := by
    have hCast : (T.card : ℝ) ≤
        ((sourceGraphGrowth (graphGrowthConstant (K + 1)) n d x - 1 : ℕ) : ℝ) := by
      exact_mod_cast hCard
    exact hCast.trans (source_graph_growth_middle_le_base hCp hdp hx hLog)
  have hsx : s ≤ x := hsBase.trans
    (source_graph_growth_base_le_coordinate (graph_growth_constant_ge_one hKp) hd hx hLog)
  have hLogS : 1 ≤ Real.log (n / s) := by
    have hRatio : n / x ≤ n / s := div_le_div_of_nonneg_left hn.le hs hsx
    exact hLog.trans (Real.log_le_log (div_pos hn hx) hRatio)
  have hCoefficient : K * (d + Real.log (n / s)) + 1 ≤
      (K + 1) * (d + Real.log (n / s) + 1) := by nlinarith
  have hMultiply := mul_le_mul_of_nonneg_right hCoefficient hs.le
  have hColumn := hA T
  have hCount : ((∑ j ∈ T, ((matrixColumnSupport A j).card + 1) : ℕ) : ℝ) =
      (∑ j ∈ T, ((matrixColumnSupport A j).card : ℝ)) + s := by
    simp [s, Finset.sum_add_distrib]
  rw [hCount]
  calc
    _ ≤ K * s * (d + Real.log (n / s)) + s := add_le_add hColumn le_rfl
    _ ≤ (K + 1) * s * (d + Real.log (n / s) + 1) := by nlinarith
    _ ≤ sourceGraphExpansion n d x / 4 :=
      source_graph_middle_degree_bound hKp hn hd hx hLog hs.le hsBase

set_option maxHeartbeats 1000000 in
theorem source_graph_ordered_gap_image_spread {ρ : Type*} [Fintype ρ]
    {m ell : ℕ} (A : Matrix ρ (Fin m) ℂ) (e : ρ ↪ Fin m) (z : ℂ)
    (v : EuclideanSpace ℂ (Fin m)) {K β n d k u : ℝ}
    (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1) (hn : 0 < n) (hd : 4 ≤ d)
    (hEll : 0 < ell) (hEllN : (ell : ℝ) ≤ n) (hLog : 1 ≤ Real.log (n / ell))
    (hLo : k ≤ ell) (hHi : (ell : ℝ) ≤ u)
    (hRank : ell + sourceGraphGrowth (graphGrowthConstant (K + 1)) n d ell ≤ m)
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K n d)
    (hUnique : MatrixUniqueExpansionBudget A e β n d k u)
    (hHeavy : MatrixHeavyRowBudget A β n d)
    (hGap : orderedNormAt (fun j => v j)
      (ell + sourceGraphGrowth (graphGrowthConstant (K + 1)) n d ell) ≤
      orderedNormAt (fun j => v j) ell * (β * ell / (d * n)) ^ 7) :
    sourceGraphExpansion n d ell / 2 ≤
      ((coordinateSpreadSet ((diagonalEmbeddedShift A e z).toEuclideanLin v)
        (β * orderedNormAt (fun j => v j) ell / 2)).card : ℝ) := by
  classical
  have hEllReal : 0 < (ell : ℝ) := by exact_mod_cast hEll
  have hKp : 0 ≤ K + 1 := by linarith
  have hCp : 0 < graphGrowthConstant (K + 1) :=
    lt_of_lt_of_le (by norm_num) (graph_growth_constant_ge_one hKp)
  have hdp : 0 < d := by linarith
  have hg := source_graph_growth_pos hCp hdp hEllReal hLog
  have hTopCard := orderedPrefix_card (fun j => v j) (by omega : ell ≤ m)
  have hUniqueTop := hUnique (orderedPrefix (fun j => v j) ell)
    (by simpa only [hTopCard] using hLo) (by simpa only [hTopCard] using hHi)
  rw [hTopCard] at hUniqueTop
  have hMiddle := source_graph_middle_support_budget A hK hn (by linarith : 1 ≤ d)
    hEllReal hLog hColumns
    (coordinateMiddleSet (orderedPrefix (fun j => v j) ell)
      (orderedPrefix (fun j => v j)
        (ell + sourceGraphGrowth (graphGrowthConstant (K + 1)) n d ell - 1)))
    (by rw [ordered_graph_middle_card _ hg hRank])
  exact unique_neighbourhood_ordered_image_spread A e z v hEll hg hRank hβ hβOne hd hn
    hEllN hz hzUpper hGap hUniqueTop (hHeavy ell hEll hLog) hMiddle

set_option maxHeartbeats 1000000 in
theorem source_graph_ordered_coordinate_no_gap {ρ : Type*} [Fintype ρ]
    {m ell : ℕ} (A : Matrix ρ (Fin m) ℂ) (e : ρ ↪ Fin m) (z : ℂ)
    (v : EuclideanSpace ℂ (Fin m)) {K β n d k u : ℝ}
    (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1) (hn : 0 < n) (hd : 4 ≤ d)
    (hEll : 0 < ell) (hEllN : (ell : ℝ) ≤ n) (hLog : 1 ≤ Real.log (n / ell))
    (hLo : k ≤ ell) (hHi : (ell : ℝ) ≤ u)
    (hRank : ell + sourceGraphGrowth (graphGrowthConstant (K + 1)) n d ell ≤ m)
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K n d)
    (hUnique : MatrixUniqueExpansionBudget A e β n d k u)
    (hHeavy : MatrixHeavyRowBudget A β n d)
    (hSmall : ‖(diagonalEmbeddedShift A e z).toEuclideanLin v‖ ^ 2 <
      sourceGraphExpansion n d ell * β ^ 2 * orderedNormAt (fun j => v j) ell ^ 2 / 8) :
    orderedNormAt (fun j => v j) ell * (β * ell / (d * n)) ^ 7 <
      orderedNormAt (fun j => v j)
        (ell + sourceGraphGrowth (graphGrowthConstant (K + 1)) n d ell) := by
  by_contra hNot
  have hGap := le_of_not_gt hNot
  have hSpread := source_graph_ordered_gap_image_spread A e z v hK hβ hβOne hn hd
    hEll hEllN hLog hLo hHi hRank hz hzUpper hColumns hUnique hHeavy hGap
  have hEnergy := image_spread_energy_lower _ hβ.le (orderedNormAt_nonneg _ _) hSpread
  exact (not_lt_of_ge hEnergy) hSmall

end CircularLaw
