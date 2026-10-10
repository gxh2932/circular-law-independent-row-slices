import CircularLaw.OrderedCoordinates

/-!
# Finite real-coordinate quantiles

Prefixes, tails and trimmed cores use the actual sorting permutation,
including repeated values. Their coordinate counts retain all integer
rounding, as needed to extract separated planar cohorts.
-/

noncomputable section
open Classical

namespace CircularLaw

def rankPrefix {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (σ.symm i).val < t)

def rankTail {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) : Finset (Fin n) :=
  Finset.univ \ rankPrefix σ (n - t)

def rankCore {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) : Finset (Fin n) :=
  Finset.univ \ (rankPrefix σ (m - 1) ∪ rankTail σ (m - 1))

theorem mem_rankPrefix {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) (i : Fin n) :
    i ∈ rankPrefix σ t ↔ (σ.symm i).val < t := by
  simp only [rankPrefix, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_rankTail {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : ℕ) (i : Fin n) :
    i ∈ rankTail σ t ↔ n - t ≤ (σ.symm i).val := by
  simp only [rankTail, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_rankPrefix, not_lt]

def rankPrefixEquiv {n t : ℕ} (σ : Equiv.Perm (Fin n)) (htn : t ≤ n) :
    ↥(rankPrefix σ t) ≃ Fin t where
  toFun i := ⟨(σ.symm i.val).val, (mem_rankPrefix σ t i.val).mp i.property⟩
  invFun j := ⟨σ ⟨j.val, lt_of_lt_of_le j.isLt htn⟩,
    (mem_rankPrefix σ t _).mpr (by simpa only [Equiv.symm_apply_apply] using j.isLt)⟩
  left_inv i := by apply Subtype.ext; exact σ.apply_symm_apply i.val
  right_inv j := by apply Fin.ext; simp only [Equiv.symm_apply_apply]

theorem rankPrefix_card {n t : ℕ} (σ : Equiv.Perm (Fin n)) (htn : t ≤ n) :
    (rankPrefix σ t).card = t := by
  rw [← Fintype.card_coe, Fintype.card_congr (rankPrefixEquiv σ htn), Fintype.card_fin]

theorem rankTail_card {n t : ℕ} (σ : Equiv.Perm (Fin n)) (htn : t ≤ n) :
    (rankTail σ t).card = t := by
  rw [rankTail, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, rankPrefix_card σ (Nat.sub_le n t)]
  omega

theorem rankPrefix_disjoint_tail {n m : ℕ} (σ : Equiv.Perm (Fin n)) (hm : 2 * m ≤ n) :
    Disjoint (rankPrefix σ m) (rankTail σ m) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hLow := (mem_rankPrefix σ m i).mp hi
  have hHigh := (mem_rankTail σ m i).mp hj
  omega

theorem rankCore_card_lower {n m : ℕ} (σ : Equiv.Perm (Fin n)) (hmn : m ≤ n) :
    n ≤ 2 * (m - 1) + (rankCore σ m).card := by
  have hBad := Finset.card_union_le (rankPrefix σ (m - 1)) (rankTail σ (m - 1))
  rw [rankPrefix_card σ (by omega), rankTail_card σ (by omega)] at hBad
  have hCard : (rankCore σ m).card = n -
      (rankPrefix σ (m - 1) ∪ rankTail σ (m - 1)).card := by
    rw [rankCore, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin]
  omega

theorem two_rankCore_inter_card_lower {n m : ℕ} (σ τ : Equiv.Perm (Fin n))
    (hmn : m ≤ n) : n ≤ 4 * (m - 1) + ((rankCore σ m) ∩ rankCore τ m).card := by
  have hσ := rankCore_card_lower σ hmn
  have hτ := rankCore_card_lower τ hmn
  have hSplit := Finset.card_union_add_card_inter (rankCore σ m) (rankCore τ m)
  have hUnion : ((rankCore σ m) ∪ rankCore τ m).card ≤ n :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  omega

theorem real_rankPrefix_value_le {n m : ℕ} (f : Fin n → ℝ)
    (hm : 0 < m) (hmn : m ≤ n) (i : Fin n) (hi : i ∈ rankPrefix (Tuple.sort f) m) :
    f i ≤ f (Tuple.sort f ⟨m - 1, by omega⟩) := by
  have hRank : (Tuple.sort f).symm i ≤ (⟨m - 1, by omega⟩ : Fin n) := by
    apply Fin.le_iff_val_le_val.mpr
    change ((Tuple.sort f).symm i).val ≤ m - 1
    have h := (mem_rankPrefix (Tuple.sort f) m i).mp hi
    omega
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using Tuple.monotone_sort f hRank

theorem real_rankTail_value_ge {n m : ℕ} (f : Fin n → ℝ)
    (hm : 0 < m) (hmn : m ≤ n) (i : Fin n) (hi : i ∈ rankTail (Tuple.sort f) m) :
    f (Tuple.sort f ⟨n - m, by omega⟩) ≤ f i := by
  have hRank : (⟨n - m, by omega⟩ : Fin n) ≤ (Tuple.sort f).symm i :=
    Fin.le_iff_val_le_val.mpr ((mem_rankTail (Tuple.sort f) m i).mp hi)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using Tuple.monotone_sort f hRank

theorem real_rankCore_value_bounds {n m : ℕ} (f : Fin n → ℝ)
    (hm : 0 < m) (hmn : m ≤ n) (i : Fin n) (hi : i ∈ rankCore (Tuple.sort f) m) :
    f (Tuple.sort f ⟨m - 1, by omega⟩) ≤ f i ∧
      f i ≤ f (Tuple.sort f ⟨n - m, by omega⟩) := by
  have hNot := (Finset.mem_sdiff.mp hi).2
  have hNotLow : i ∉ rankPrefix (Tuple.sort f) (m - 1) :=
    fun h => hNot (Finset.mem_union_left _ h)
  have hNotHigh : i ∉ rankTail (Tuple.sort f) (m - 1) :=
    fun h => hNot (Finset.mem_union_right _ h)
  have hLow : m - 1 ≤ ((Tuple.sort f).symm i).val := by
    rw [mem_rankPrefix] at hNotLow
    omega
  have hHigh : ((Tuple.sort f).symm i).val ≤ n - m := by
    rw [mem_rankTail] at hNotHigh
    omega
  have hRankLow : (⟨m - 1, by omega⟩ : Fin n) ≤ (Tuple.sort f).symm i := by
    apply Fin.le_iff_val_le_val.mpr
    exact hLow
  have hRankHigh : (Tuple.sort f).symm i ≤ (⟨n - m, by omega⟩ : Fin n) := by
    apply Fin.le_iff_val_le_val.mpr
    exact hHigh
  exact ⟨by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      Tuple.monotone_sort f hRankLow,
    by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      Tuple.monotone_sort f hRankHigh⟩

theorem real_quantile_gap_cohorts {n m : ℕ} (f : Fin n → ℝ)
    (hm : 0 < m) (hHalf : 2 * m ≤ n) {τ : ℝ}
    (hGap : τ ≤ f (Tuple.sort f ⟨n - m, by omega⟩) -
      f (Tuple.sort f ⟨m - 1, by omega⟩)) :
    ∃ I J : Finset (Fin n), Disjoint I J ∧ I.card = m ∧ J.card = m ∧
      ∀ i ∈ I, ∀ j ∈ J, τ ≤ f j - f i := by
  have hmn : m ≤ n := by omega
  refine ⟨rankPrefix (Tuple.sort f) m, rankTail (Tuple.sort f) m,
    rankPrefix_disjoint_tail _ hHalf, rankPrefix_card _ hmn, rankTail_card _ hmn, ?_⟩
  intro i hi j hj
  have hLow := real_rankPrefix_value_le f hm hmn i hi
  have hHigh := real_rankTail_value_ge f hm hmn j hj
  linarith

end CircularLaw
