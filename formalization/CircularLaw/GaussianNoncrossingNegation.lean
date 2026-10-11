import CircularLaw.GaussianFirstPairDecomposition

/-!
# Exchanging direct and adjoint symbols preserves the noncrossing count

Complementing the word exchanges the position fibers and reverses the
matching. The four distinct endpoints give the same noncrossing condition
with the pair orientations reversed. The resulting injective maps in
both directions prove equality of the finite counts.
-/

noncomputable section
open Classical

namespace CircularLaw

def gaussianNegatedDirectEquiv {α : Type*} (b : α → Bool) :
    GaussianDirectPositions (fun v => !b v) ≃ GaussianAdjointPositions b :=
  Equiv.subtypeEquivRight (fun v => by
    change (Bool.not (b v) = false ↔ b v = true)
    cases b v <;> decide)

def gaussianNegatedAdjointEquiv {α : Type*} (b : α → Bool) :
    GaussianAdjointPositions (fun v => !b v) ≃ GaussianDirectPositions b :=
  Equiv.subtypeEquivRight (fun v => by
    change (Bool.not (b v) = true ↔ b v = false)
    cases b v <;> decide)

def gaussianWordPairingNegation {α : Type*} (b : α → Bool) :
    GaussianWordPairing b ≃ GaussianWordPairing (fun v => !b v) :=
  (Equiv.symmEquiv (GaussianDirectPositions b) (GaussianAdjointPositions b)).trans
    (Equiv.equivCongr (gaussianNegatedDirectEquiv b).symm (gaussianNegatedAdjointEquiv b).symm)

theorem gaussian_word_pairing_negation_image {α : Type*} (b : α → Bool)
    (e : GaussianWordPairing b) (a : GaussianDirectPositions (fun v => !b v)) :
    ((gaussianWordPairingNegation b e) a).val = (e.symm (gaussianNegatedDirectEquiv b a)).val := rfl

theorem gaussian_word_noncrossing_negation {n : ℕ} (b : Fin n → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) :
    GaussianWordNoncrossing (fun v => !b v) (gaussianWordPairingNegation b e) := by
  intro a c hca
  let a' := e.symm (gaussianNegatedDirectEquiv b a)
  let c' := e.symm (gaussianNegatedDirectEquiv b c)
  have hOldNe : c' ≠ a' := by
    intro h
    have h' := congrArg e h
    simp only [a', c', Equiv.apply_symm_apply] at h'
    exact hca ((gaussianNegatedDirectEquiv b).injective h')
  have h := hNC a' c' hOldNe
  have hImageA : (e a').val = a.val :=
    congrArg Subtype.val (e.apply_symm_apply (gaussianNegatedDirectEquiv b a))
  have hImageC : (e c').val = c.val :=
    congrArg Subtype.val (e.apply_symm_apply (gaussianNegatedDirectEquiv b c))
  rw [hImageA, hImageC] at h
  rw [gaussian_word_pairing_negation_image, gaussian_word_pairing_negation_image]
  change finiteCircularCut a.val a'.val c.val ↔ finiteCircularCut a.val a'.val c'.val
  have hAA : a'.val ≠ a.val :=
    gaussian_direct_adjoint_positions_ne b a' (gaussianNegatedDirectEquiv b a)
  have hAC : a'.val ≠ c.val :=
    gaussian_direct_adjoint_positions_ne b a' (gaussianNegatedDirectEquiv b c)
  have hCA : c'.val ≠ a.val :=
    gaussian_direct_adjoint_positions_ne b c' (gaussianNegatedDirectEquiv b a)
  have hCC : c'.val ≠ c.val :=
    gaussian_direct_adjoint_positions_ne b c' (gaussianNegatedDirectEquiv b c)
  have hAdjNe : c.val ≠ a.val := fun h => hca (Subtype.ext h)
  have hDirNe : c'.val ≠ a'.val := fun h => hOldNe (Subtype.ext h)
  simp only [finiteCircularCut] at h ⊢
  split_ifs at h ⊢ <;> omega

theorem gaussian_noncrossing_card_le_negation {n : ℕ} (b : Fin n → Bool) :
    Fintype.card (GaussianNoncrossingPairings b) ≤
      Fintype.card (GaussianNoncrossingPairings (fun v => !b v)) := by
  apply Fintype.card_le_of_injective
    (fun e : GaussianNoncrossingPairings b =>
      (⟨gaussianWordPairingNegation b e.val, gaussian_word_noncrossing_negation b e.val e.property⟩ :
        GaussianNoncrossingPairings (fun v => !b v)))
  intro x y h
  exact Subtype.ext ((gaussianWordPairingNegation b).injective (congrArg Subtype.val h))

theorem gaussian_noncrossing_card_negation {n : ℕ} (b : Fin n → Bool) :
    Fintype.card (GaussianNoncrossingPairings (fun v => !b v)) =
      Fintype.card (GaussianNoncrossingPairings b) := by
  apply Nat.le_antisymm
  · simpa only [Bool.not_not] using gaussian_noncrossing_card_le_negation (fun v => !b v)
  · exact gaussian_noncrossing_card_le_negation b

end CircularLaw
