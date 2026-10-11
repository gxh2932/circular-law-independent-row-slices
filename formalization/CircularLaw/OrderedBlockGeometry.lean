import CircularLaw.OrderedCoordinates

/-!
# Equal-size disjoint blocks from ordered ranks

Each block uses consecutive ranks from a literal permutation of the
coordinates. Blocks at the top and after a tail offset are disjoint when
the total top length is at most that offset.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def orderedBlockIndex {n q s : ℕ} (offset : ℕ) (hFit : offset + q * s ≤ n)
    (p : Fin q × Fin s) : Fin n :=
  ⟨offset + (finProdFinEquiv p).val, by
    have h := (finProdFinEquiv p).isLt
    omega⟩

theorem orderedBlockIndex_injective {n q s : ℕ} (offset : ℕ)
    (hFit : offset + q * s ≤ n) : Function.Injective (orderedBlockIndex offset hFit) := by
  intro a b h
  apply finProdFinEquiv.injective
  apply Fin.ext
  have hVal := congrArg Fin.val h
  change offset + (finProdFinEquiv a).val = offset + (finProdFinEquiv b).val at hVal
  omega

def orderedRankBlock {n q s : ℕ} (σ : Equiv.Perm (Fin n))
    (offset : ℕ) (hFit : offset + q * s ≤ n) (b : Fin q) : Finset (Fin n) :=
  Finset.univ.image (fun t : Fin s => σ (orderedBlockIndex offset hFit (b, t)))

theorem orderedRankBlock_card {n q s : ℕ} (σ : Equiv.Perm (Fin n))
    (offset : ℕ) (hFit : offset + q * s ≤ n) (b : Fin q) :
    (orderedRankBlock σ offset hFit b).card = s := by
  rw [orderedRankBlock, Finset.card_image_of_injective]
  · exact Finset.card_fin _
  · intro a c h
    have hPair := orderedBlockIndex_injective offset hFit (σ.injective h)
    exact congrArg Prod.snd hPair

theorem orderedRankBlock_nonempty {n q s : ℕ} (σ : Equiv.Perm (Fin n))
    (offset : ℕ) (hFit : offset + q * s ≤ n) (hs : 0 < s) (b : Fin q) :
    (orderedRankBlock σ offset hFit b).Nonempty := by
  rw [← Finset.card_pos, orderedRankBlock_card]
  exact hs

theorem orderedRankBlock_rank_bounds {n q s : ℕ} (σ : Equiv.Perm (Fin n))
    (offset : ℕ) (hFit : offset + q * s ≤ n) (b : Fin q) {j : Fin n}
    (hj : j ∈ orderedRankBlock σ offset hFit b) :
    offset ≤ (σ.symm j).val ∧ (σ.symm j).val < offset + q * s := by
  rcases Finset.mem_image.mp hj with ⟨t, _, rfl⟩
  simp only [Equiv.symm_apply_apply, orderedBlockIndex]
  have h := (finProdFinEquiv (b, t)).isLt
  omega

theorem orderedRankBlock_pairwise {n q s : ℕ} (σ : Equiv.Perm (Fin n))
    (offset : ℕ) (hFit : offset + q * s ≤ n) :
    Pairwise (fun a b => Disjoint (orderedRankBlock σ offset hFit a)
      (orderedRankBlock σ offset hFit b)) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro j hja hjb
  rcases Finset.mem_image.mp hja with ⟨t, _, ht⟩
  rcases Finset.mem_image.mp hjb with ⟨u, _, hu⟩
  have hPair := orderedBlockIndex_injective offset hFit
    (σ.injective (ht.trans hu.symm))
  exact hab (congrArg Prod.fst hPair)

theorem orderedRankBlock_top_tail_disjoint {n q s : ℕ} (σ : Equiv.Perm (Fin n))
    (tail : ℕ) (hTop : q * s ≤ n) (hTail : tail + q * s ≤ n)
    (hGap : q * s ≤ tail) (a b : Fin q) :
    Disjoint (orderedRankBlock σ 0 (by simpa only [zero_add] using hTop) a)
      (orderedRankBlock σ tail hTail b) := by
  apply Finset.disjoint_left.mpr
  intro j hjTop hjTail
  have hT := orderedRankBlock_rank_bounds σ 0 (by simpa only [zero_add] using hTop) a hjTop
  have hR := orderedRankBlock_rank_bounds σ tail hTail b hjTail
  omega

theorem orderedRankBlock_union_pairwise {n q s : ℕ} (σ : Equiv.Perm (Fin n))
    (tail : ℕ) (hTop : q * s ≤ n) (hTail : tail + q * s ≤ n)
    (hGap : q * s ≤ tail) :
    Pairwise (fun a b => Disjoint
      (orderedRankBlock σ 0 (by simpa only [zero_add] using hTop) a ∪
        orderedRankBlock σ tail hTail a)
      (orderedRankBlock σ 0 (by simpa only [zero_add] using hTop) b ∪
        orderedRankBlock σ tail hTail b)) := by
  intro a b hab
  apply Finset.disjoint_union_left.mpr
  constructor
  · apply Finset.disjoint_union_right.mpr
    exact ⟨orderedRankBlock_pairwise σ 0 _ hab,
      orderedRankBlock_top_tail_disjoint σ tail hTop hTail hGap a b⟩
  · apply Finset.disjoint_union_right.mpr
    exact ⟨(orderedRankBlock_top_tail_disjoint σ tail hTop hTail hGap b a).symm,
      orderedRankBlock_pairwise σ tail hTail hab⟩

theorem norm_ordered_blocks_separated {n q s : ℕ} (y : Fin n → ℂ)
    (tail : ℕ) (lastTop : Fin n) (hTop : q * s ≤ n) (hTail : tail + q * s ≤ n)
    (hLength : q * s ≤ lastTop.val + 1) {r : ℝ}
    (hGap : ∀ j : Fin n, tail ≤ j.val → 2 * r + orderedNorm y j < orderedNorm y lastTop)
    (b : Fin q) (l : Fin n)
    (hl : l ∈ orderedRankBlock (normOrderPerm y) 0 (by simpa only [zero_add] using hTop) b)
    (j : Fin n) (hj : j ∈ orderedRankBlock (normOrderPerm y) tail hTail b) :
    2 * r < dist (y l) (y j) := by
  have hL := orderedRankBlock_rank_bounds (normOrderPerm y) 0 _ b hl
  have hR := orderedRankBlock_rank_bounds (normOrderPerm y) tail hTail b hj
  have hRank : (normOrderPerm y).symm l ≤ lastTop := by
    apply Fin.le_iff_val_le_val.mpr
    omega
  have hNorm := orderedNorm_antitone y hRank
  have hSep := (hGap ((normOrderPerm y).symm j) hR.1).trans_le hNorm
  rw [orderedNorm_of_rank, orderedNorm_of_rank] at hSep
  exact norm_gap_implies_equal_block_separation hSep

end CircularLaw
