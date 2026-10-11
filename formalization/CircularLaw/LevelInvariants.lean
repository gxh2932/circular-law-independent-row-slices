import CircularLaw.CanonicalParts
import Mathlib.Data.Nat.Log

/-!
# Level nesting and permutation invariants

The selected counts depend only on initial level multiplicities. The
represented value sets, spread and regular heights, and part sizes are
therefore invariant under permutation of the original coordinates. The
represented sets are nested, and their nonempty orders have a logarithmic
upper bound.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

theorem levelRemainder_card_eq {α β : Type*} [LinearOrder α] [LinearOrder β]
    (s : Finset α) (t : Finset β) (h : s.card = t.card) (j : ℕ) :
    (levelRemainder s j).card = (levelRemainder t j).card := by
  induction j with
  | zero => exact h
  | succ j ih => rw [levelRemainder_card_succ, levelRemainder_card_succ, ih]

theorem selectedLevel_card_eq {α β : Type*} [LinearOrder α] [LinearOrder β]
    (s : Finset α) (t : Finset β) (h : s.card = t.card) (j : ℕ) :
    (orderChunk (levelRemainder s j) j).card = (orderChunk (levelRemainder t j) j).card := by
  rw [orderChunk_card, orderChunk_card, levelRemainder_card_eq s t h j]

def initialLevelPermEquiv {n : ℕ} (y : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (z : ℂ) :
    {i : Fin n // i ∈ initialLevel (y ∘ σ) z} ≃ {i : Fin n // i ∈ initialLevel y z} where
  toFun i := ⟨σ i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp i.property).2⟩⟩
  invFun i := ⟨σ.symm i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      (Finset.mem_filter.mp i.property).2⟩⟩
  left_inv i := by apply Subtype.ext; exact σ.symm_apply_apply _
  right_inv i := by apply Subtype.ext; exact σ.apply_symm_apply _

theorem initialLevel_card_perm {n : ℕ} (y : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (z : ℂ) :
    (initialLevel (y ∘ σ) z).card = (initialLevel y z).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (initialLevelPermEquiv y σ z)

theorem selectedLevelAt_card_perm {n : ℕ} (y : Fin n → ℂ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (z : ℂ) : (selectedLevelAt (y ∘ σ) j z).card = (selectedLevelAt y j z).card :=
  selectedLevel_card_eq _ _ (initialLevel_card_perm y σ z) j

theorem representedValues_perm {n : ℕ} (y : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (j : ℕ) :
    representedValues (y ∘ σ) j = representedValues y j := by
  ext z
  rw [← selectedLevelAt_nonempty_mem, ← selectedLevelAt_nonempty_mem,
    ← Finset.card_pos, ← Finset.card_pos, selectedLevelAt_card_perm]

theorem spreadValueSet_perm {n : ℕ} (y : Fin n → ℂ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (δ : ℝ) : spreadValueSet (y ∘ σ) j δ = spreadValueSet y j δ := by
  unfold spreadValueSet
  rw [representedValues_perm]

theorem regularValueSet_perm {n : ℕ} (y : Fin n → ℂ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (δ : ℝ) : regularValueSet (y ∘ σ) j δ = regularValueSet y j δ := by
  rw [regularValueSet, regularValueSet, representedValues_perm, spreadValueSet_perm]

theorem levelPart_card_perm {n : ℕ} (y : Fin n → ℂ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (A : Finset ℂ) : (levelPart (y ∘ σ) j A).card = (levelPart y j A).card := by
  rw [levelPart_card, levelPart_card]
  exact Finset.sum_congr rfl (fun z _ => selectedLevelAt_card_perm y σ j z)

theorem source_parts_perm {n : ℕ} (y : Fin n → ℂ) (σ : Equiv.Perm (Fin n))
    (j : ℕ) (δ : ℝ) :
    (spreadValueSet (y ∘ σ) j δ).card = (spreadValueSet y j δ).card ∧
    (regularValueSet (y ∘ σ) j δ).card = (regularValueSet y j δ).card ∧
    (spreadPart (y ∘ σ) j δ).card = (spreadPart y j δ).card ∧
    (regularPart (y ∘ σ) j δ).card = (regularPart y j δ).card := by
  rw [spreadValueSet_perm, regularValueSet_perm]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [spreadPart, spreadPart, spreadValueSet_perm, levelPart_card_perm]
  · rw [regularPart, regularPart, regularValueSet_perm, levelPart_card_perm]

theorem representedValues_antitone {n : ℕ} (y : Fin n → ℂ) :
    Antitone (representedValues y) := by
  intro j l hjl z hz
  have hL := (selectedLevelAt_nonempty_mem y l z).mpr hz
  have hR := (orderChunk_nonempty_iff _ _).mp hL
  obtain ⟨i, hi⟩ := hR
  have hiJ := levelRemainder_antitone (initialLevel y z) hjl hi
  exact (selectedLevelAt_nonempty_mem y j z).mp
    ((orderChunk_nonempty_iff _ _).mpr ⟨i, hiJ⟩)

theorem totalHeight_antitone {n : ℕ} (y : Fin n → ℂ) :
    Antitone (fun j => (representedValues y j).card) :=
  fun _ _ h => Finset.card_le_card (representedValues_antitone y h)

theorem representedValues_empty_of_log_bound {n : ℕ} (y : Fin n → ℂ)
    {j : ℕ} (hj : Nat.log 2 n + 2 ≤ j) : representedValues y j = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro h
  obtain ⟨z, hz⟩ := h
  have hLow := (selectedLevel_card_bounds (initialLevel y z) j
    ((selectedLevelAt_nonempty_mem y j z).mpr hz)).1
  have hHigh : (selectedLevelAt y j z).card ≤ n := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq
      (by simp only [Finset.card_univ, Fintype.card_fin])
  have hPow : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hIndex : Nat.log 2 n + 1 ≤ j - 1 := by omega
  have hMono := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hIndex
  exact (not_le_of_gt hPow) (hMono.trans (hLow.trans hHigh))

end CircularLaw
