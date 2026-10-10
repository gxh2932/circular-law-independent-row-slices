import CircularLaw.SingletonWitnessLower

/-!
# Quantitative row witness bounds

The lower bounds use the exact one- and two-coordinate laws inside a row.
They do not assume that the coordinates of a fixed-size support are independent.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem unique_row_witness_probability_nine_tenths {n d : ℕ} (hn : 2 ≤ n)
    (hd : 0 < d) (hdn : d ≤ n) (L J : Finset (Fin n)) (hLJ : L ⊆ J)
    (hLoss : ((d : ℝ) - 1) * ((J.card : ℝ) - 1) / ((n : ℝ) - 1) ≤ 1 / 10) :
    (9 / 10 : ℝ) * d * L.card / n ≤
      uniformProbability (uniqueRowWitness (d := d) L J) := by
  have h := unique_row_witness_probability_lower hn hd hdn L J hLJ
  have hScale : (0 : ℝ) ≤ (d : ℝ) * L.card / n := by positivity
  calc
    _ = (9 / 10 : ℝ) * ((d : ℝ) * L.card / n) := by ring
    _ ≤ ((d : ℝ) * L.card / n) *
        (1 - ((d : ℝ) - 1) * ((J.card : ℝ) - 1) / ((n : ℝ) - 1)) := by
      nlinarith
    _ ≤ _ := h

theorem small_set_witness_loss {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (J : Finset (Fin n)) (hSmall : 4 * d * J.card ≤ n) :
    ((d : ℝ) - 1) * ((J.card : ℝ) - 1) / ((n : ℝ) - 1) ≤ 1 / 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hSmallR : (4 : ℝ) * d * J.card ≤ n := by exact_mod_cast hSmall
  have hNumerator : ((d : ℝ) - 1) * ((J.card : ℝ) - 1) ≤ (d : ℝ) * J.card := by
    calc
      _ ≤ ((d : ℝ) - 1) * J.card :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) - 1)).mpr
  nlinarith

theorem small_set_unique_witness_probability {n d : ℕ} (hn : 2 ≤ n)
    (hd : 0 < d) (hdn : d ≤ n) (L J : Finset (Fin n)) (hLJ : L ⊆ J)
    (hSmall : 4 * d * J.card ≤ n) :
    (d : ℝ) * L.card / (2 * n) ≤
      uniformProbability (uniqueRowWitness (d := d) L J) := by
  have h := unique_row_witness_probability_lower hn hd hdn L J hLJ
  have hLoss := small_set_witness_loss hn hd J hSmall
  have hScale : (0 : ℝ) ≤ (d : ℝ) * L.card / n := by positivity
  have hRewrite : (d : ℝ) * L.card / (2 * n) = ((d : ℝ) * L.card / n) / 2 := by ring
  rw [hRewrite]
  nlinarith

theorem small_set_block_witness_probability {n d : ℕ} (hn : 2 ≤ n)
    (hd : 0 < d) (hdn : d ≤ n) (J : Finset (Fin n))
    (hSmall : 4 * d * J.card ≤ n) :
    (d : ℝ) * J.card / (2 * n) ≤
      uniformProbability (fun S : RowSlice n d => (S.val ∩ J).card = 1) := by
  have h := small_set_unique_witness_probability hn hd hdn J J (fun _ hj => hj) hSmall
  exact h.trans (uniformProbability_mono (fun S hS => (uniqueRowWitness_self_iff J S).mp hS))

theorem equal_pair_block_witness_probability {n d s : ℕ} (hn : 2 ≤ n)
    (hd : 0 < d) (hdn : d ≤ n) (L R : Finset (Fin n))
    (hDis : Disjoint L R) (hL : L.card = s) (hR : R.card = s)
    (hSmall : 100 * d * s ≤ n) :
    (d : ℝ) * s / n ≤
      uniformProbability (fun S : RowSlice n d => (S.val ∩ (L ∪ R)).card = 1) := by
  have hCard : (L ∪ R).card = 2 * s := by
    rw [Finset.card_union_of_disjoint hDis, hL, hR]
    omega
  have hDense : 4 * d * (L ∪ R).card ≤ n := by
    rw [hCard]
    nlinarith
  have h := small_set_block_witness_probability hn hd hdn (L ∪ R) hDense
  rw [hCard, Nat.cast_mul, Nat.cast_ofNat] at h
  convert h using 1
  ring

end CircularLaw
