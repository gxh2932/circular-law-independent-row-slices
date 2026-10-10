import CircularLaw.SingletonWitnessLower
import CircularLaw.SingletonExposureConcentration

/-!
# Rare-selection small balls under the exact row-slice law

Expose the selected coordinates outside a single equal-halves block. On
singleton-intersection fibers, the selected position is uniform in that
block and a separated disk has conditional probability at most one half.
The exact singleton law supplies the resulting exclusion probability.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem singletonWitnessMask_one_block_card {n d : ℕ} (J : Finset (Fin n))
    (S : RowSlice n d) :
    (singletonWitnessMask (fun _ : Unit => J) S).card =
      if (S.val ∩ J).card = 1 then 1 else 0 := by
  by_cases h : (S.val ∩ J).card = 1 <;> simp [singletonWitnessMask, h]

theorem row_slice_equal_halves_small_ball {n d : ℕ} (hdn : d ≤ n)
    (L R : Finset (Fin n)) (hDis : Disjoint L R) (hSize : L.card = R.card)
    (hLeft : L.Nonempty) (y : Fin n → ℂ) {r : ℝ} (hr : 0 < r)
    (hSep : ∀ l ∈ L, ∀ j ∈ R, 2 * r < dist (y l) (y j)) (z : ℂ) :
    uniformProbability (fun S : RowSlice n d => ‖rowLinearForm S y - z‖ ≤ r) ≤
      1 - uniformProbability (fun S : RowSlice n d => (S.val ∩ (L ∪ R)).card = 1) / 2 := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  let J := fun _ : Unit => L ∪ R
  let E := fun S : RowSlice n d => ‖rowLinearForm S y - z‖ ≤ r
  let w := fun S : RowSlice n d =>
    if (S.val ∩ (L ∪ R)).card = 1 then (1 / 2 : ℝ) else 1
  have hConstant : ∀ S T : RowSlice n d,
      singletonExposure J S = singletonExposure J T → w S = w T := by
    intro S T h
    have hCard := congrArg (fun a => a.1.card) h
    change (singletonWitnessMask J S).card = (singletonWitnessMask J T).card at hCard
    rw [singletonWitnessMask_one_block_card, singletonWitnessMask_one_block_card] at hCard
    dsimp only [w]
    split_ifs with hS hT <;> simp_all
  have hFiber (S : RowSlice n d) :
      uniformProbability (fun T : {T : RowSlice n d // singletonExposure J T = singletonExposure J S} =>
        E T.val) ≤ w S := by
    by_cases hS : (S.val ∩ (L ∪ R)).card = 1
    · have hb : 1 ≤ (singletonWitnessMask J S).card := by
        rw [singletonWitnessMask_one_block_card, if_pos hS]
      have h := equal_block_exposure_small_ball (fun _ : Unit => L) (fun _ => R)
        (by intro q p hne; exact False.elim (hne (Subsingleton.elim q p)))
        (fun _ => hDis) (fun _ => hSize) (fun _ => hLeft) S hb y hr
        (fun _ => hSep) 0 z
      change uniformProbability (fun T : {T : RowSlice n d // singletonExposure J T = singletonExposure J S} =>
        ‖rowLinearForm T.val y + 0 - z‖ ≤ r) ≤ _ at h
      simpa only [E, w, if_pos hS, add_zero] using h.trans (min_le_left _ _)
    · simpa only [w, if_neg hS] using uniformProbability_le_one
        (fun T : {T : RowSlice n d // singletonExposure J T = singletonExposure J S} => E T.val)
  have hBound := uniformProbability_le_fiber_reference (singletonExposure J) E w hConstant hFiber
  have hWeight : w = fun S : RowSlice n d =>
      1 - (1 / 2 : ℝ) * (if (S.val ∩ (L ∪ R)).card = 1 then (1 : ℝ) else 0) := by
    funext S
    dsimp only [w]
    split_ifs <;> norm_num
  rw [hWeight, finiteMean_sub, finiteMean_const, finiteMean_const_mul,
    finiteMean_indicator] at hBound
  convert hBound using 1
  ring

theorem slice_singleton_block_probability_lower_half {n d : ℕ} (hn : 2 ≤ n)
    (hd : 0 < d) (hdn : d ≤ n) (J : Finset (Fin n))
    (hCollision : ((d : ℝ) - 1) * ((J.card : ℝ) - 1) / ((n : ℝ) - 1) ≤ 1 / 2) :
    (J.card : ℝ) * ((d : ℝ) / n) / 2 ≤
      uniformProbability (fun S : RowSlice n d => (S.val ∩ J).card = 1) := by
  have h := unique_row_witness_probability_lower hn hd hdn J J (Finset.Subset.refl _)
  have hEvent : uniqueRowWitness (d := d) J J =
      (fun S : RowSlice n d => (S.val ∩ J).card = 1) := by
    funext S
    exact propext (uniqueRowWitness_self_iff J S)
  rw [hEvent] at h
  have hFactor := mul_le_mul_of_nonneg_left
    (show (1 / 2 : ℝ) ≤ 1 - ((d : ℝ) - 1) * ((J.card : ℝ) - 1) / ((n : ℝ) - 1) by linarith)
    (by positivity : 0 ≤ (d : ℝ) * J.card / n)
  have hLower : (J.card : ℝ) * ((d : ℝ) / n) / 2 ≤
      (d : ℝ) * J.card / n *
        (1 - ((d : ℝ) - 1) * ((J.card : ℝ) - 1) / ((n : ℝ) - 1)) := by
    convert hFactor using 1
    ring
  exact hLower.trans h

theorem rare_slice_equal_halves_collision_bound {n d m : ℕ} (hn : 2 ≤ n)
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hm : 0 < m)
    (hRare : m = 1 ∨ (m : ℝ) * ((d : ℝ) / n) ≤ 1 / 4) :
    ((d : ℝ) - 1) * (2 * (m : ℝ) - 1) / ((n : ℝ) - 1) ≤ 1 / 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hDegreeR : 2 * (d : ℝ) ≤ n := by exact_mod_cast hDegree
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) - 1)).mpr
  rcases hRare with rfl | hRare
  · norm_num
    linarith
  · have hRareMul := (div_le_iff₀ (by linarith : (0 : ℝ) < n)).mp
      (show (m : ℝ) * d / n ≤ 1 / 4 by simpa only [mul_div_assoc] using hRare)
    nlinarith

theorem row_slice_rare_equal_halves_small_ball {n d m : ℕ} (hn : 2 ≤ n)
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hm : 0 < m)
    (hRare : m = 1 ∨ (m : ℝ) * ((d : ℝ) / n) ≤ 1 / 4)
    (L R : Finset (Fin n)) (hDis : Disjoint L R) (hL : L.card = m) (hR : R.card = m)
    (y : Fin n → ℂ) {t : ℝ} (ht : 0 < t)
    (hSep : ∀ l ∈ L, ∀ j ∈ R, t ≤ dist (y l) (y j)) (z : ℂ) :
    uniformProbability (fun S : RowSlice n d => ‖rowLinearForm S y - z‖ ≤ t / 3) ≤
      1 - (m : ℝ) * ((d : ℝ) / n) / 2 := by
  have hdn : d ≤ n := by omega
  have hLeft : L.Nonempty := Finset.card_pos.mp (by omega)
  have hCard : (L ∪ R).card = 2 * m := by rw [Finset.card_union_of_disjoint hDis, hL, hR]; omega
  have hCollision := rare_slice_equal_halves_collision_bound hn hd hDegree hm hRare
  have hMass := slice_singleton_block_probability_lower_half hn hd hdn (L ∪ R)
    (by simpa only [hCard, Nat.cast_mul, Nat.cast_ofNat] using hCollision)
  have hSmall := row_slice_equal_halves_small_ball hdn L R hDis (hL.trans hR.symm)
    hLeft y (by linarith : 0 < t / 3)
    (fun l hl j hj => (by linarith : 2 * (t / 3) < t).trans_le (hSep l hl j hj)) z
  rw [hCard, Nat.cast_mul, Nat.cast_ofNat] at hMass
  linarith

end CircularLaw
