import CircularLaw.GaussianNoncrossingNegation

/-!
# Alternating direct and adjoint positions

Parity parametrizes the actual direct and adjoint position fibers. The
interior of a first pair reverses the alternating colors, while the final
interval keeps them. These identities apply to the exact reindexed words.
-/

noncomputable section
open Classical

namespace CircularLaw

def finiteParityPositionsEquiv (n r : ℕ) (hr : r < 2) :
    Fin ((n + 1 - r) / 2) ≃ {a : Fin n // a.val % 2 = r} where
  toFun a := ⟨⟨2 * a.val + r, by have := a.isLt; omega⟩, by
    change (2 * a.val + r) % 2 = r
    omega⟩
  invFun a := ⟨a.val.val / 2, by have := a.val.isLt; have := a.property; omega⟩
  left_inv a := by
    apply Fin.ext
    simp only
    omega
  right_inv a := by
    apply Subtype.ext
    apply Fin.ext
    simp only
    have := a.property
    omega

def gaussianAlternatingWord (n : ℕ) (a : Fin n) : Bool := decide (a.val % 2 = 1)

def gaussianAlternatingDirectEquiv (n : ℕ) :
    GaussianDirectPositions (gaussianAlternatingWord n) ≃ Fin ((n + 1) / 2) :=
  (Equiv.subtypeEquivRight (fun a : Fin n => by
    change (decide (a.val % 2 = 1) = false ↔ a.val % 2 = 0)
    simp only [decide_eq_false_iff_not]
    omega)).trans (finiteParityPositionsEquiv n 0 (by decide)).symm

def gaussianAlternatingAdjointEquiv (n : ℕ) :
    GaussianAdjointPositions (gaussianAlternatingWord n) ≃ Fin (n / 2) := by
  refine (Equiv.subtypeEquivRight (q := fun a : Fin n => a.val % 2 = 1)
    (fun a : Fin n => ?_)).trans ?_
  · change (decide (a.val % 2 = 1) = true ↔ a.val % 2 = 1)
    exact decide_eq_true_iff
  · simpa only [Nat.add_sub_cancel] using (finiteParityPositionsEquiv n 1 (by decide)).symm

def gaussianAlternatingEvenAdjointEquiv (k : ℕ) :
    Fin k ≃ GaussianAdjointPositions (gaussianAlternatingWord (2 * k)) where
  toFun a := ⟨⟨2 * a.val + 1, by have := a.isLt; omega⟩, by
    simp only [gaussianAlternatingWord, decide_eq_true_eq]
    omega⟩
  invFun a := ⟨a.val.val / 2, by have := a.val.isLt; omega⟩
  left_inv a := by
    apply Fin.ext
    simp only
    omega
  right_inv a := by
    apply Subtype.ext
    apply Fin.ext
    simp only
    have h := a.property
    simp only [gaussianAlternatingWord, decide_eq_true_eq] at h
    omega

def gaussianAlternatingNoncrossingCount (n : ℕ) : ℕ :=
  Fintype.card (GaussianNoncrossingPairings (gaussianAlternatingWord n))

theorem gaussian_alternating_noncrossing_zero : gaussianAlternatingNoncrossingCount 0 = 1 :=
  gaussian_noncrossing_empty_card _

theorem gaussian_alternating_noncrossing_odd (k : ℕ) :
    gaussianAlternatingNoncrossingCount (2 * k + 1) = 0 := by
  letI : IsEmpty (GaussianNoncrossingPairings (gaussianAlternatingWord (2 * k + 1))) := ⟨by
    intro e
    have h := Fintype.card_congr e.val
    have hD := Fintype.card_congr (gaussianAlternatingDirectEquiv (2 * k + 1))
    have hA := Fintype.card_congr (gaussianAlternatingAdjointEquiv (2 * k + 1))
    simp only [Fintype.card_fin] at hD hA
    rw [hD, hA] at h
    omega⟩
  exact Fintype.card_eq_zero

theorem gaussian_alternating_interior_word {k : ℕ} (q : Fin (k + 1)) :
    gaussianAlternatingWord (k + 1) ∘ gaussianFirstInteriorMap q =
      fun a => !gaussianAlternatingWord (q.val - 1) a := by
  funext a
  simp only [Function.comp_apply, gaussianAlternatingWord, gaussianFirstInteriorMap]
  by_cases h : a.val % 2 = 1
  · have h' : (a.val + 1) % 2 = 0 := by omega
    simp [h, h']
  · have h' : (a.val + 1) % 2 = 1 := by omega
    simp [h, h']

theorem gaussian_alternating_outer_word {k : ℕ}
    (q : GaussianAdjointPositions (gaussianAlternatingWord (k + 1))) :
    gaussianAlternatingWord (k + 1) ∘ gaussianFirstOuterMap q.val =
      gaussianAlternatingWord (k - q.val.val) := by
  have h := q.property
  simp only [gaussianAlternatingWord, decide_eq_true_eq] at h
  funext a
  simp only [Function.comp_apply, gaussianAlternatingWord, gaussianFirstOuterMap]
  have hMod : (q.val.val + 1 + a.val) % 2 = a.val % 2 := by omega
  simp only [hMod]

theorem gaussian_alternating_interior_count {k : ℕ} (q : Fin (k + 1)) :
    Fintype.card (GaussianNoncrossingPairings
      (gaussianAlternatingWord (k + 1) ∘ gaussianFirstInteriorMap q)) =
      gaussianAlternatingNoncrossingCount (q.val - 1) := by
  rw [gaussian_alternating_interior_word, gaussian_noncrossing_card_negation]
  rfl

theorem gaussian_alternating_outer_count {k : ℕ}
    (q : GaussianAdjointPositions (gaussianAlternatingWord (k + 1))) :
    Fintype.card (GaussianNoncrossingPairings
      (gaussianAlternatingWord (k + 1) ∘ gaussianFirstOuterMap q.val)) =
      gaussianAlternatingNoncrossingCount (k - q.val.val) := by
  rw [gaussian_alternating_outer_word]
  rfl

end CircularLaw
