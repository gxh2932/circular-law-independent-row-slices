import CircularLaw.RankQuantiles
import Mathlib.Data.Int.Interval

/-!
# Separated quantiles for finite integer orders

Each selected order has bounded coordinate mass. Trimming the two
quantile tails then forces the remaining selected coordinates to occupy
a long integer interval. All endpoints use the actual coordinate order,
including ties, and all counts retain integer rounding.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem integer_interval_selected_mass {n : ℕ} (B : Fin n → ℤ)
    (S : Finset (Fin n)) {a b : ℤ} (hab : a ≤ b) {M : ℝ}
    (hBins : ∀ j : ℤ, ((S.filter (fun i => B i = j)).card : ℝ) ≤ M) :
    ((S.filter (fun i => a ≤ B i ∧ B i ≤ b)).card : ℝ) ≤
      ((b : ℝ) - a + 1) * M := by
  have hFiber := Finset.sum_card_fiberwise_eq_card_filter S (Finset.Icc a b) B
  have hCount : ((Finset.Icc a b).card : ℝ) = (b : ℝ) - a + 1 := by
    have h := Int.card_Icc_of_le a b (show a ≤ b + 1 by omega)
    have hR : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - a := by exact_mod_cast h
    linarith
  calc
    _ = ∑ j ∈ Finset.Icc a b, ((S.filter (fun i => B i = j)).card : ℝ) := by
      simpa only [Finset.mem_Icc, Nat.cast_sum] using congrArg (fun t : ℕ => (t : ℝ)) hFiber.symm
    _ ≤ ∑ _j ∈ Finset.Icc a b, M := Finset.sum_le_sum (fun j _ => hBins j)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hCount]

theorem integer_order_quantile_gap {n m : ℕ} (B : Fin n → ℤ)
    (S : Finset (Fin n)) (hm : 0 < m) (hHalf : 2 * m ≤ n) {M : ℝ}
    (hBins : ∀ j : ℤ, ((S.filter (fun i => B i = j)).card : ℝ) ≤ M) :
    ∃ b₁ b₂ : ℤ, b₁ ≤ b₂ ∧
      m ≤ (Finset.univ.filter (fun i => B i ≤ b₁)).card ∧
      m ≤ (Finset.univ.filter (fun i => b₂ ≤ B i)).card ∧
      (S.card : ℝ) - 2 * (m - 1 : ℕ) ≤ ((b₂ : ℝ) - b₁ + 1) * M := by
  let f : Fin n → ℝ := fun i => (B i : ℝ)
  let σ := Tuple.sort f
  let b₁ := B (σ ⟨m - 1, by omega⟩)
  let b₂ := B (σ ⟨n - m, by omega⟩)
  have hmn : m ≤ n := by omega
  have hOrder : b₁ ≤ b₂ := by
    have hRanks : (⟨m - 1, by omega⟩ : Fin n) ≤ ⟨n - m, by omega⟩ := by
      apply Fin.le_iff_val_le_val.mpr
      change m - 1 ≤ n - m
      omega
    have hSorted := Tuple.monotone_sort f hRanks
    change (b₁ : ℝ) ≤ b₂ at hSorted
    exact_mod_cast hSorted
  have hLower : m ≤ (Finset.univ.filter (fun i => B i ≤ b₁)).card := by
    rw [← rankPrefix_card σ hmn]
    apply Finset.card_le_card
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := real_rankPrefix_value_le f hm hmn i hi
    change (B i : ℝ) ≤ b₁ at h
    exact_mod_cast h
  have hUpper : m ≤ (Finset.univ.filter (fun i => b₂ ≤ B i)).card := by
    rw [← rankTail_card σ hmn]
    apply Finset.card_le_card
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := real_rankTail_value_ge f hm hmn i hi
    change (b₂ : ℝ) ≤ B i at h
    exact_mod_cast h
  have hCore := rankCore_card_lower σ hmn
  have hSplit := Finset.card_union_add_card_inter S (rankCore σ m)
  have hUnion : (S ∪ rankCore σ m).card ≤ n :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hTrim : S.card ≤ 2 * (m - 1) + (S ∩ rankCore σ m).card := by omega
  have hSubset : S ∩ rankCore σ m ⊆ S.filter (fun i => b₁ ≤ B i ∧ B i ≤ b₂) := by
    intro i hi
    obtain ⟨hiS, hiCore⟩ := Finset.mem_inter.mp hi
    have h := real_rankCore_value_bounds f hm hmn i hiCore
    change (b₁ : ℝ) ≤ B i ∧ (B i : ℝ) ≤ b₂ at h
    exact Finset.mem_filter.mpr ⟨hiS, by exact_mod_cast h⟩
  have hTrimR : (S.card : ℝ) ≤ 2 * (m - 1 : ℕ) + (S ∩ rankCore σ m).card := by
    exact_mod_cast hTrim
  have hCardR : ((S ∩ rankCore σ m).card : ℝ) ≤
      (S.filter (fun i => b₁ ≤ B i ∧ B i ≤ b₂)).card := by
    exact_mod_cast Finset.card_le_card hSubset
  have hMass := integer_interval_selected_mass B S hOrder hBins
  exact ⟨b₁, b₂, hOrder, hLower, hUpper, by linarith⟩

theorem integer_order_small_mass_quantiles {n : ℕ} (hn : 4 ≤ n)
    (B : Fin n → ℤ) (S : Finset (Fin n)) {R M : ℝ}
    (hR : 0 < R) (hRn : R ≤ n) (hSmall : R / 4 ≤ S.card)
    (hBins : ∀ j : ℤ, ((S.filter (fun i => B i = j)).card : ℝ) ≤ M) :
    ∃ b₁ b₂ : ℤ, b₁ ≤ b₂ ∧
      R / 16 ≤ ((Finset.univ.filter (fun i => B i ≤ b₁)).card : ℝ) ∧
      R / 16 ≤ ((Finset.univ.filter (fun i => b₂ ≤ B i)).card : ℝ) ∧
      R / 8 ≤ ((b₂ : ℝ) - b₁ + 1) * M := by
  let m := ⌈R / 16⌉₊
  have hmLower : R / 16 ≤ (m : ℝ) := Nat.le_ceil _
  have hmUpper : (m : ℝ) < R / 16 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm : 0 < m := by
    have h : (0 : ℝ) < m := by linarith
    exact_mod_cast h
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hHalf : 2 * m ≤ n := by
    have h : (2 : ℝ) * m ≤ n := by linarith
    exact_mod_cast h
  have hPred : (m - 1 : ℕ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  obtain ⟨b₁, b₂, hOrder, hLow, hHigh, hGap⟩ := integer_order_quantile_gap B S hm hHalf hBins
  have hLowR : (m : ℝ) ≤ (Finset.univ.filter (fun i => B i ≤ b₁)).card := by exact_mod_cast hLow
  have hHighR : (m : ℝ) ≤ (Finset.univ.filter (fun i => b₂ ≤ B i)).card := by exact_mod_cast hHigh
  rw [hPred] at hGap
  exact ⟨b₁, b₂, hOrder, hmLower.trans hLowR, hmLower.trans hHighR, by linarith⟩

end CircularLaw
