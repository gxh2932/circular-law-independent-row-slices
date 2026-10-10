import CircularLaw.RowLoadSurvival
import CircularLaw.AlmostConstantRowAction

/-!
# The four source coordinate sets for an almost-constant vector

These are the literal sets `J1`, `J2`, `J3`, and `J4`, using the actual
decreasing-norm permutation. Avoiding `J2` controls every selected
nonclose coordinate by the `n0` modulus. Its total load is bounded by
the loads in `J3` and `J4`.
-/

noncomputable section
open Classical

namespace CircularLaw

def almostConstantBadTop {n : ℕ} (x : Fin n → ℂ) (r k : ℕ) (θ : ℝ) (c : ℂ) :
    Finset (Fin n) := orderedPrefix x r \ almostConstantCoordinates x k θ c

def almostConstantMiddle {n : ℕ} (x : Fin n → ℂ) (r k : ℕ) (θ : ℝ) (c : ℂ) :
    Finset (Fin n) := orderedPrefix x k \ (almostConstantCoordinates x k θ c ∪
      almostConstantBadTop x r k θ c)

def almostConstantFarTail {n : ℕ} (x : Fin n → ℂ) (k : ℕ) (θ : ℝ) (c : ℂ) :
    Finset (Fin n) := Finset.univ \ (almostConstantCoordinates x k θ c ∪ orderedPrefix x k)

theorem almost_constant_row_sets_size {n r k : ℕ} (hrn : r ≤ n) (hkn : k ≤ n)
    (x : Fin n → ℂ) (θ : ℝ) (c : ℂ)
    (hMany : n - k < (almostConstantCoordinates x k θ c).card) :
    (almostConstantBadTop x r k θ c).card ≤ r ∧
      (almostConstantMiddle x r k θ c).card ≤ k ∧
      (almostConstantFarTail x k θ c).card ≤ k := by
  have hTop : (almostConstantBadTop x r k θ c).card ≤ r :=
    (Finset.card_le_card Finset.sdiff_subset).trans_eq (orderedPrefix_card x hrn)
  have hMiddle : (almostConstantMiddle x r k θ c).card ≤ k :=
    (Finset.card_le_card Finset.sdiff_subset).trans_eq (orderedPrefix_card x hkn)
  have hSub : almostConstantFarTail x k θ c ⊆ Finset.univ \ almostConstantCoordinates x k θ c := by
    intro j hj
    rcases Finset.mem_sdiff.mp hj with ⟨hUniv, hNot⟩
    exact Finset.mem_sdiff.mpr ⟨hUniv, fun h => hNot (Finset.mem_union_left _ h)⟩
  have hCard := Finset.card_le_card hSub
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin] at hCard
  exact ⟨hTop, hMiddle, by omega⟩

theorem row_load_below_one_avoids {n d : ℕ} (S : RowSlice n d) (J : Finset (Fin n))
    (hLoad : (rowLoad S J : ℝ) < 1) : ∀ j ∈ S.val, j ∉ J := by
  have hNat : rowLoad S J < 1 := by exact_mod_cast hLoad
  have hZero : (S.val ∩ J).card = 0 := by change rowLoad S J = 0; omega
  have hEmpty := Finset.card_eq_zero.mp hZero
  intro j hj hjJ
  have h := Finset.mem_inter.mpr ⟨hj, hjJ⟩
  rw [hEmpty] at h
  exact Finset.notMem_empty j h

theorem almost_constant_selected_bad_load {n d r k : ℕ} (S : RowSlice n d)
    (x : Fin n → ℂ) (θ : ℝ) (c : ℂ)
    (hAvoid : ∀ j ∈ S.val, j ∉ almostConstantBadTop x r k θ c) :
    ((S.val \ almostConstantCoordinates x k θ c).card : ℝ) ≤
      (rowLoad S (almostConstantMiddle x r k θ c) : ℝ) +
        rowLoad S (almostConstantFarTail x k θ c) := by
  have hSub : S.val \ almostConstantCoordinates x k θ c ⊆
      (S.val ∩ almostConstantMiddle x r k θ c) ∪ (S.val ∩ almostConstantFarTail x k θ c) := by
    intro j hj
    rcases Finset.mem_sdiff.mp hj with ⟨hjS, hjF⟩
    by_cases hjTop : j ∈ orderedPrefix x k
    · apply Finset.mem_union_left
      exact Finset.mem_inter.mpr ⟨hjS, Finset.mem_sdiff.mpr ⟨hjTop, by
        intro hUnion
        rcases Finset.mem_union.mp hUnion with hF | hBad
        · exact hjF hF
        · exact hAvoid j hjS hBad⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hjS, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, by
        intro hUnion
        rcases Finset.mem_union.mp hUnion with hF | hTop
        · exact hjF hF
        · exact hjTop hTop⟩⟩
  have hCard := (Finset.card_le_card hSub).trans (Finset.card_union_le _ _)
  exact_mod_cast hCard

theorem almost_constant_nonclose_norm {n d r k : ℕ} (hr : 0 < r) (hrn : r ≤ n)
    (S : RowSlice n d) (x : Fin n → ℂ) (θ : ℝ) (c : ℂ)
    (hAvoid : ∀ j ∈ S.val, j ∉ almostConstantBadTop x r k θ c)
    (hS : orderedNormAt x r ≤ 12 * orderedNormAt x k)
    (hCenter : ‖c‖ ≤ (1 + θ) * orderedNormAt x k) :
    ∀ j ∈ S.val \ almostConstantCoordinates x k θ c,
      ‖x j - c‖ ≤ (13 + θ) * orderedNormAt x k := by
  intro j hj
  rcases Finset.mem_sdiff.mp hj with ⟨hjS, hjF⟩
  have hjTop : j ∉ orderedPrefix x r := fun h =>
    hAvoid j hjS (Finset.mem_sdiff.mpr ⟨h, hjF⟩)
  have hNorm := (norm_le_orderedNormAt_notMem_prefix x hr hrn j hjTop).trans hS
  have hTriangle := norm_sub_le (x j) c
  nlinarith

end CircularLaw
