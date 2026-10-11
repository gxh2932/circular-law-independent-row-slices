import CircularLaw.UniqueNeighbourhoodAmplification
import CircularLaw.OrderedNormAt

/-!
# The source coordinate-gap scale and actual ordered coordinates

The seventh-power coordinate gap controls the tail at the fifth-power
row-mass threshold. The ordered prefix of size ell+g-1 leaves a tail
bounded by the literal one-based order statistic at ell+g.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

theorem norm_le_ordered_norm_at_outside_predecessor {n k : ℕ}
    (v : Fin n → ℂ) (hk : 0 < k) (hkn : k ≤ n) (j : Fin n)
    (hj : j ∉ orderedPrefix v (k - 1)) : ‖v j‖ ≤ orderedNormAt v k := by
  rw [orderedNormAt_eq v hk hkn]
  have hRank : (⟨k - 1, by omega⟩ : Fin n) ≤ (normOrderPerm v).symm j := by
    apply Fin.le_iff_val_le_val.mpr
    change k - 1 ≤ ((normOrderPerm v).symm j).val
    have hNot : ¬((normOrderPerm v).symm j).val < k - 1 := fun h =>
      hj ((mem_orderedPrefix v (k - 1) j).mpr h)
    omega
  simpa only [orderedNorm_of_rank] using orderedNorm_antitone v hRank

theorem source_graph_gap_row_budget {β d n ell : ℝ}
    (hβ : 0 < β) (hβOne : β ≤ 1) (hd : 4 ≤ d)
    (hn : 0 < n) (hEll : 0 < ell) (hEllN : ell ≤ n) :
    ((d * n / (β * ell)) ^ 5 / β + d) * (β * ell / (d * n)) ^ 7 ≤ β / 2 := by
  let r := β * ell / (d * n)
  have hdPos : 0 < d := by linarith
  have hr : 0 < r := div_pos (mul_pos hβ hEll) (mul_pos hdPos hn)
  have hDr : d * r ≤ β := by
    have hEq : d * r = β * (ell / n) := by
      dsimp [r]
      field_simp
    rw [hEq]
    exact (mul_le_mul_of_nonneg_left ((div_le_one hn).mpr hEllN) hβ.le).trans_eq (mul_one β)
  have h4r : 4 * r ≤ β := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) hr.le]
  have hrQuarter : r ≤ 1 / 4 := by linarith
  have hrOne : r ≤ 1 := by linarith
  have hPow : r ^ 7 ≤ r ^ 2 := pow_le_pow_of_le_one hr.le hrOne (by decide : 2 ≤ 7)
  have hFirst : r ^ 2 / β ≤ β / 16 := by
    apply (div_le_iff₀ hβ).mpr
    nlinarith [sq_nonneg (β - 4 * r)]
  have hSecond : d * r ^ 7 ≤ β / 4 := by
    calc
      d * r ^ 7 ≤ d * r ^ 2 := mul_le_mul_of_nonneg_left hPow hdPos.le
      _ = (d * r) * r := by ring
      _ ≤ β * r := mul_le_mul_of_nonneg_right hDr hr.le
      _ ≤ β / 4 := by nlinarith
  have hIdentity : ((d * n / (β * ell)) ^ 5 / β + d) * r ^ 7 =
      r ^ 2 / β + d * r ^ 7 := by
    dsimp [r]
    field_simp
  change ((d * n / (β * ell)) ^ 5 / β + d) * r ^ 7 ≤ β / 2
  rw [hIdentity]
  linarith

theorem ordered_graph_middle_card {n ell g : ℕ} (v : Fin n → ℂ)
    (hg : 0 < g) (hRank : ell + g ≤ n) :
    (coordinateMiddleSet (orderedPrefix v ell) (orderedPrefix v (ell + g - 1))).card = g - 1 := by
  classical
  unfold coordinateMiddleSet
  rw [@Finset.card_sdiff_of_subset (Fin n)
    (orderedPrefix v ell) (orderedPrefix v (ell + g - 1))
    (fun a b => Classical.propDecidable (a = b))
    (orderedPrefix_subset v (by omega : ell ≤ ell + g - 1)),
    orderedPrefix_card v (by omega : ell + g - 1 ≤ n),
    orderedPrefix_card v (by omega : ell ≤ n)]
  omega

set_option maxHeartbeats 1000000 in
theorem unique_neighbourhood_ordered_image_spread {ρ : Type*} [Fintype ρ]
    {m ell g : ℕ} (A : Matrix ρ (Fin m) ℂ) (e : ρ ↪ Fin m) (z : ℂ)
    (v : EuclideanSpace ℂ (Fin m)) (hEll : 0 < ell) (hg : 0 < g)
    (hRank : ell + g ≤ m) {β d n b : ℝ}
    (hβ : 0 < β) (hβOne : β ≤ 1) (hd : 4 ≤ d) (hn : 0 < n)
    (hEllN : (ell : ℝ) ≤ n) (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hGap : orderedNormAt (fun j => v j) (ell + g) ≤
      orderedNormAt (fun j => v j) ell * (β * ell / (d * n)) ^ 7)
    (hUnique : b ≤ ((matrixUniqueNeighbourhood A e β
      (orderedPrefix (fun j => v j) ell)).card : ℝ))
    (hHeavy : ((matrixHeavyRows A ((d * n / (β * ell)) ^ 5 / β)).card : ℝ) ≤ b / 4)
    (hColumns : ((∑ j ∈ coordinateMiddleSet (orderedPrefix (fun j => v j) ell)
      (orderedPrefix (fun j => v j) (ell + g - 1)), ((matrixColumnSupport A j).card + 1) : ℕ) : ℝ) ≤ b / 4) :
    b / 2 ≤ ((coordinateSpreadSet ((diagonalEmbeddedShift A e z).toEuclideanLin v)
      (β * orderedNormAt (fun j => v j) ell / 2)).card : ℝ) := by
  classical
  have hEllReal : 0 < (ell : ℝ) := by exact_mod_cast hEll
  have hdPos : 0 < d := by linarith
  refine unique_neighbourhood_image_spread_of_budgets A e z v
    (orderedPrefix (fun j => v j) ell) (orderedPrefix (fun j => v j) (ell + g - 1))
    (orderedPrefix_subset _ (by omega)) hβ.le (orderedNormAt_nonneg _ _)
    (by positivity : 0 ≤ (β * ell / (d * n)) ^ 7) hz hzUpper ?_ ?_
    (source_graph_gap_row_budget hβ hβOne hd hn hEllReal hEllN) hUnique hHeavy hColumns
  · intro j hj
    exact orderedNormAt_le_norm_mem_prefix _ hEll (by omega) j hj
  · intro j hj
    have hNot : j ∉ orderedPrefix (fun j => v j) (ell + g - 1) := by
      simpa only [Finset.mem_compl] using hj
    have hTail := norm_le_ordered_norm_at_outside_predecessor
      (fun j => v j) (by omega : 0 < ell + g) hRank j hNot
    exact hTail.trans (by simpa only [mul_comm] using hGap)

end CircularLaw
