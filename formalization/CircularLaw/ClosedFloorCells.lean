import CircularLaw.FloorGridCover
import Mathlib.Combinatorics.Pigeonhole

/-!
# Closed cluster disks and repeated rounded values

A closed disk of radius `1/k` meets at most nine floor cells. Finite
pigeonhole counting therefore produces an actual rounded value repeated
on at least one ninth of a coordinate cluster.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem floor_index_within_one_le {a b : ℝ} (h : |a - b| ≤ 1) :
    ⌊b⌋ - 1 ≤ ⌊a⌋ ∧ ⌊a⌋ ≤ ⌊b⌋ + 1 := by
  have hLow : b - 1 ≤ a := by have h' := (abs_le.mp h).1; linarith
  have hHigh : a ≤ b + 1 := by have h' := (abs_le.mp h).2; linarith
  exact ⟨by simpa only [Int.floor_sub_one] using Int.floor_mono hLow,
    by simpa only [Int.floor_add_one] using Int.floor_mono hHigh⟩

theorem floorIndexPair_mem_closed_nearby_cells {k : ℕ} (hk : 0 < k) {z w : ℂ}
    (h : dist z w ≤ 1 / (k : ℝ)) :
    floorIndexPair k z ∈
      (Finset.Icc ((floorIndexPair k w).1 - 1) ((floorIndexPair k w).1 + 1)) ×ˢ
      (Finset.Icc ((floorIndexPair k w).2 - 1) ((floorIndexPair k w).2 + 1)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hRe : |(k : ℝ) * z.re - (k : ℝ) * w.re| ≤ 1 := by
    rw [← mul_sub, abs_mul, abs_of_pos hkR]
    have hCoord : |z.re - w.re| ≤ 1 / (k : ℝ) :=
      (Complex.abs_re_le_norm (z - w)).trans (by simpa only [dist_eq_norm] using h)
    have hMul := (le_div_iff₀ hkR).mp hCoord
    nlinarith
  have hIm : |(k : ℝ) * z.im - (k : ℝ) * w.im| ≤ 1 := by
    rw [← mul_sub, abs_mul, abs_of_pos hkR]
    have hCoord : |z.im - w.im| ≤ 1 / (k : ℝ) :=
      (Complex.abs_im_le_norm (z - w)).trans (by simpa only [dist_eq_norm] using h)
    have hMul := (le_div_iff₀ hkR).mp hCoord
    nlinarith
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (floor_index_within_one_le hRe),
    Finset.mem_Icc.mpr (floor_index_within_one_le hIm)⟩

theorem canonicalApprox_repeated_from_cluster {n k : ℕ} (hk : 0 < k)
    (x : Fin n → ℂ) (c : ℂ) {δ ρ : ℝ} (hρ : ρ ≤ 1 / (k : ℝ))
    (hCluster : δ * n ≤ ((Finset.univ.filter (fun i => ‖x i - c‖ ≤ ρ)).card : ℝ)) :
    ∃ z : ℂ, δ * n / 9 ≤ (initialLevel (fun i => canonicalApprox k (x i)) z).card := by
  let S := Finset.univ.filter (fun i => ‖x i - c‖ ≤ ρ)
  let T := (Finset.Icc ((floorIndexPair k c).1 - 1) ((floorIndexPair k c).1 + 1)) ×ˢ
    (Finset.Icc ((floorIndexPair k c).2 - 1) ((floorIndexPair k c).2 + 1))
  let f := fun i => floorIndexPair k (x i)
  have hT : T.card = 9 := nearby_floor_cells_card _ _
  have hTNonempty : T.Nonempty := Finset.card_pos.mp (by rw [hT]; norm_num)
  have hMap : ∀ i ∈ S, f i ∈ T := by
    intro i hi
    apply floorIndexPair_mem_closed_nearby_cells hk
    simpa only [dist_eq_norm] using (Finset.mem_filter.mp hi).2.trans hρ
  have hMass : T.card • (δ * (n : ℝ) / 9) ≤ (S.card : ℝ) := by
    rw [hT, nsmul_eq_mul]
    change 9 * (δ * (n : ℝ) / 9) ≤ (S.card : ℝ)
    linarith
  obtain ⟨ab, _, hFiber⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hMap hTNonempty hMass
  refine ⟨gridValue k ab.1 ab.2, hFiber.trans ?_⟩
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hiS, hiF⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact congrArg (fun p : ℤ × ℤ => gridValue k p.1 p.2) hiF

end CircularLaw
