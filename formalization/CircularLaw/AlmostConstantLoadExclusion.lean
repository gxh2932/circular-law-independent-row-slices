import CircularLaw.AlmostConstantRowSets

/-!
# Almost-constant kernel exclusion on the actual row-load event

For a vector in the manuscript's `B(10/d^3) ∩ S(12)`, the literal four
coordinate sets leave at least half the rows. Their actual retained
shifted matrix action has modulus at least `d*x*_{n3}/2`. Positivity of
the `S(12)` modulus therefore rules out membership in the kernel.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem almostConstantRadius_le_hundredth {d : ℕ} (hd : 10 ≤ d) :
    0 ≤ almostConstantRadius d ∧ almostConstantRadius d ≤ 1 / 100 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hCube : (1000 : ℝ) ≤ (d : ℝ) ^ 3 := by
    exact_mod_cast Nat.pow_le_pow_left hd 3
  unfold almostConstantRadius
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ (pow_pos hdR 3)).mpr
  linarith

theorem source_almost_constant_surviving_action {n d : ℕ} {a₃ : ℝ}
    (hd : 10 ≤ d) (hn : 0 < n) (hRank : 0 < almostConstantRank n d)
    (hRankN : almostConstantRank n d ≤ n) (hk : 0 < thirdSteepScale n a₃)
    (hHalf : 2 * thirdSteepScale n a₃ ≤ n)
    (hScale : (thirdSteepScale n a₃ : ℝ) ≤ (n : ℝ) / 1000)
    (I : Finset (Fin n)) (hRows : (99 / 100 : ℝ) * n ≤ I.card)
    (rows : RowSliceMatrix n d) (hLoad : SourceRowLoad I (thirdSteepScale n a₃) rows)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ (d : ℝ) / 20) (x : Fin n → ℂ)
    (hB : x ∈ sourceAlmostConstant n d a₃) (hS : x ∈ sourceS n d a₃ 12) :
    ∃ G : Finset (Fin n), G ⊆ I ∧ (n : ℝ) / 2 ≤ G.card ∧
      ∀ i : I, i.val ∈ G →
        (d : ℝ) / 2 * orderedNormAt x (thirdSteepScale n a₃) ≤
          ‖(retainedShiftedMatrix I ζ rows).mulVec x i‖ := by
  let k := thirdSteepScale n a₃
  let θ := almostConstantRadius d
  obtain ⟨c, hMany⟩ := hB
  let F := almostConstantCoordinates x k θ c
  let J₂ := almostConstantBadTop x (almostConstantRank n d) k θ c
  let J₃ := almostConstantMiddle x (almostConstantRank n d) k θ c
  let J₄ := almostConstantFarTail x k θ c
  let top := orderedPrefix x k
  let G := rowLoadSurvivors I top J₂ J₃ J₄ k rows
  have hkn : k ≤ n := by change thirdSteepScale n a₃ ≤ n; omega
  have hSizes := almost_constant_row_sets_size hRankN hkn x θ c hMany
  have hTop : (top.card : ℝ) ≤ (n : ℝ) / 1000 := by
    rw [show top.card = k from orderedPrefix_card x hkn]
    exact hScale
  have hCard := source_row_load_survivors_half (top := top) hLoad hSizes.1 hSizes.2.1 hSizes.2.2
    hRows hTop
  have hCenter := almost_constant_center_bounds hk hHalf x θ c hMany
  have hRadius := almostConstantRadius_le_hundredth hd
  refine ⟨G, ?_, hCard, ?_⟩
  · exact Finset.sdiff_subset
  · intro i hi
    have hGood := rowLoadSurvivors_mem hi
    have hAvoid := row_load_below_one_avoids (rows i.val) J₂ hGood.2.2.1
    have hSelected := almost_constant_selected_bad_load (rows i.val) x θ c hAvoid
    have hBadLoad : (((rows i.val).val \ F).card : ℝ) ≤ 32 * (k : ℝ) * d / n := by
      change (((rows i.val).val \ F).card : ℝ) ≤
        (rowLoad (rows i.val) J₃ : ℝ) + rowLoad (rows i.val) J₄ at hSelected
      calc
        _ ≤ (rowLoad (rows i.val) J₃ : ℝ) + rowLoad (rows i.val) J₄ := hSelected
        _ ≤ 16 * (k : ℝ) * d / n + 16 * (k : ℝ) * d / n :=
          add_le_add hGood.2.2.2.1.le hGood.2.2.2.2.le
        _ = _ := by ring
    have hIndex := norm_le_orderedNormAt_notMem_prefix x hk hkn i.val hGood.2.1
    have hFar := almost_constant_nonclose_norm hRank hRankN (rows i.val) x θ c hAvoid hS.2 hCenter.2
    rw [retainedShiftedMatrix_mulVec]
    apply source_almost_constant_row_lower hn (rows i.val) F x c ζ i.val hRadius.1 hRadius.2
      (orderedNormAt_nonneg x k) hCenter.1 hIndex ?_ hFar hBadLoad hScale hShift
    intro j hj
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hj).2).2

theorem source_almost_constant_load_kernel_exclusion {n d : ℕ} {a₃ : ℝ}
    (hd : 10 ≤ d) (hn : 0 < n) (hRank : 0 < almostConstantRank n d)
    (hRankN : almostConstantRank n d ≤ n) (hk : 0 < thirdSteepScale n a₃)
    (hHalf : 2 * thirdSteepScale n a₃ ≤ n)
    (hScale : (thirdSteepScale n a₃ : ℝ) ≤ (n : ℝ) / 1000)
    (I : Finset (Fin n)) (hRows : (99 / 100 : ℝ) * n ≤ I.card)
    (rows : RowSliceMatrix n d) (hLoad : SourceRowLoad I (thirdSteepScale n a₃) rows)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ (d : ℝ) / 20) :
    ∀ x ∈ sourceAlmostConstant n d a₃ ∩ sourceS n d a₃ 12,
      (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0 := by
  intro x hx hKernel
  obtain ⟨G, hGI, hCard, hAction⟩ := source_almost_constant_surviving_action hd hn hRank hRankN
    hk hHalf hScale I hRows rows hLoad ζ hShift x hx.1 hx.2
  have hPositive : (0 : ℝ) < orderedNormAt x (thirdSteepScale n a₃) := by
    have hS := hx.2
    change 0 < orderedNormAt x (almostConstantRank n d) ∧
      orderedNormAt x (almostConstantRank n d) ≤ 12 * orderedNormAt x (thirdSteepScale n a₃) at hS
    linarith
  have hGPos : (0 : ℝ) < G.card := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hG : 0 < G.card := by exact_mod_cast hGPos
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hG
  have hLower := hAction ⟨i, hGI hi⟩ hi
  have hZero := congrFun hKernel ⟨i, hGI hi⟩
  rw [hZero] at hLower
  simp only [Pi.zero_apply, norm_zero] at hLower
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hStrict : (0 : ℝ) < (d : ℝ) / 2 * orderedNormAt x (thirdSteepScale n a₃) := by positivity
  linarith

end CircularLaw
