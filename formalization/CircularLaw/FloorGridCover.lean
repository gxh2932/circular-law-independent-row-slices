import CircularLaw.GridBox
import CircularLaw.CanonicalParts

/-!
# Nine-cell bound for coarse grid values

A disk of radius `1/k` meets at most nine different canonical coarse
cells. For a family on which coarse rounding is injective, the canonical
spread selection must therefore contain at least one ninth as many
values, as soon as that family contains ten values. This supplies the
geometric step in LLTTY19 Lemma 5.9 directly, without assuming a packing
conclusion for the source greedy construction.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def floorIndexPair (k : ℕ) (z : ℂ) : ℤ × ℤ :=
  (⌊(k : ℝ) * z.re⌋, ⌊(k : ℝ) * z.im⌋)

theorem floor_index_within_one {a b : ℝ} (h : |a - b| < 1) :
    ⌊b⌋ - 1 ≤ ⌊a⌋ ∧ ⌊a⌋ ≤ ⌊b⌋ + 1 := by
  have hLow : b - 1 ≤ a := by have h' := (abs_lt.mp h).1; linarith
  have hHigh : a ≤ b + 1 := by have h' := (abs_lt.mp h).2; linarith
  constructor
  · simpa only [Int.floor_sub_one] using Int.floor_mono hLow
  · simpa only [Int.floor_add_one] using Int.floor_mono hHigh

theorem floorIndexPair_mem_nearby_cells {k : ℕ} (hk : 0 < k) {z w : ℂ}
    (h : dist z w < 1 / (k : ℝ)) :
    floorIndexPair k z ∈
      (Finset.Icc ((floorIndexPair k w).1 - 1) ((floorIndexPair k w).1 + 1)) ×ˢ
      (Finset.Icc ((floorIndexPair k w).2 - 1) ((floorIndexPair k w).2 + 1)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hRe : |(k : ℝ) * z.re - (k : ℝ) * w.re| < 1 := by
    rw [← mul_sub, abs_mul, abs_of_pos hkR]
    have hCoord : |z.re - w.re| < 1 / (k : ℝ) :=
      (Complex.abs_re_le_norm (z - w)).trans_lt (by simpa only [dist_eq_norm] using h)
    have hMul := (lt_div_iff₀ hkR).mp hCoord
    nlinarith
  have hIm : |(k : ℝ) * z.im - (k : ℝ) * w.im| < 1 := by
    rw [← mul_sub, abs_mul, abs_of_pos hkR]
    have hCoord : |z.im - w.im| < 1 / (k : ℝ) :=
      (Complex.abs_im_le_norm (z - w)).trans_lt (by simpa only [dist_eq_norm] using h)
    have hMul := (lt_div_iff₀ hkR).mp hCoord
    nlinarith
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (floor_index_within_one hRe),
    Finset.mem_Icc.mpr (floor_index_within_one hIm)⟩

theorem nearby_floor_cells_card (a b : ℤ) :
    ((Finset.Icc (a - 1) (a + 1)) ×ˢ (Finset.Icc (b - 1) (b + 1))).card = 9 := by
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
  have ha : (a + 1 + 1 - (a - 1)).toNat = 3 := by omega
  have hb : (b + 1 + 1 - (b - 1)).toNat = 3 := by omega
  rw [ha, hb]

theorem coarse_injective_disk_card_le_nine {k : ℕ} (hk : 0 < k) (A : Finset ℂ)
    (hInj : Set.InjOn (canonicalApprox k) A) (w : ℂ)
    (hA : ∀ z ∈ A, dist z w < 1 / (k : ℝ)) : A.card ≤ 9 := by
  calc
    A.card ≤ ((Finset.Icc ((floorIndexPair k w).1 - 1) ((floorIndexPair k w).1 + 1)) ×ˢ
        (Finset.Icc ((floorIndexPair k w).2 - 1) ((floorIndexPair k w).2 + 1))).card := by
      apply Finset.card_le_card_of_injOn (floorIndexPair k)
      · intro z hz
        exact floorIndexPair_mem_nearby_cells hk (hA z hz)
      · intro z hz v hv hzv
        apply hInj hz hv
        exact congrArg (fun ab : ℤ × ℤ => gridValue k ab.1 ab.2) hzv
    _ = 9 := nearby_floor_cells_card _ _

theorem coarse_injective_small_diameter_card_le_nine {k : ℕ} (hk : 0 < k)
    (A : Finset ℂ) (hInj : Set.InjOn (canonicalApprox k) A)
    (hA : ∀ z ∈ A, ∀ w ∈ A, dist z w < 1 / (k : ℝ)) : A.card ≤ 9 := by
  by_cases hNonempty : A.Nonempty
  · obtain ⟨w, hw⟩ := hNonempty
    exact coarse_injective_disk_card_le_nine hk A hInj w (fun z hz => hA z hz w hw)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hNonempty, Finset.card_empty]
    norm_num

theorem coarse_injective_spreadSelection_height {k : ℕ} (hk : 0 < k)
    (Λ A : Finset ℂ) (hA : A ⊆ Λ) (hInj : Set.InjOn (canonicalApprox k) A)
    (hTen : 10 ≤ A.card) :
    letI := complexLexOrder
    A.card ≤ 9 * (spreadSelection (1 / (k : ℝ)) Λ).card := by
  letI := complexLexOrder
  let S := spreadSelection (1 / (k : ℝ)) Λ
  have hδ : 0 < 1 / (k : ℝ) := one_div_pos.mpr (by exact_mod_cast hk)
  have hPair : (pairCapable (1 / (k : ℝ)) Λ).Nonempty := by
    by_contra hNo
    have hClose := (pairCapable_empty_iff (1 / (k : ℝ)) Λ).mp
      (Finset.not_nonempty_iff_eq_empty.mp hNo)
    have hCount := coarse_injective_small_diameter_card_le_nine hk A hInj
      (fun z hz w hw => hClose z (hA hz) w (hA hw))
    omega
  have hCover : A ⊆ S.biUnion (fun w => A.filter (fun z => dist z w < 1 / (k : ℝ))) := by
    intro z hz
    by_cases hzS : z ∈ S
    · exact Finset.mem_biUnion.mpr ⟨z, hzS, Finset.mem_filter.mpr ⟨hz, by simpa using hδ⟩⟩
    · obtain ⟨w, hw, hDist⟩ := spreadSelection_covers (1 / (k : ℝ)) Λ hPair z (hA hz) hzS
      exact Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_filter.mpr ⟨hz, hDist⟩⟩
  calc
    A.card ≤ (S.biUnion (fun w => A.filter (fun z => dist z w < 1 / (k : ℝ)))).card :=
      Finset.card_le_card hCover
    _ ≤ ∑ w ∈ S, (A.filter (fun z => dist z w < 1 / (k : ℝ))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ S, 9 := Finset.sum_le_sum (fun w _ =>
      coarse_injective_disk_card_le_nine hk _ (hInj.mono (Finset.filter_subset _ _)) w
        (fun z hz => (Finset.mem_filter.mp hz).2))
    _ = 9 * S.card := by simp [mul_comm]

end CircularLaw
