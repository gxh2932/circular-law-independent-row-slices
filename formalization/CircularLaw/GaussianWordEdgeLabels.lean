import CircularLaw.GaussianWordPairingCounts

/-!
# The exact two position occurrences of a Gaussian pairing label

Each direct position labels its matched adjoint position. Every position
has exactly that label, and its unordered quotient endpoints are those
of the direct edge, reversed on the adjoint branch. The label fibers
are precisely the actual two matched positions.
-/

noncomputable section
open Classical

namespace CircularLaw

def gaussianWordPositionLabel {α : Type*} (b : α → Bool) (e : GaussianWordPairing b)
    (v : α) : GaussianDirectPositions b :=
  if h : b v = false then ⟨v, h⟩ else e.symm ⟨v, Bool.eq_true_of_not_eq_false h⟩

theorem gaussian_word_position_label_direct {α : Type*} (b : α → Bool)
    (e : GaussianWordPairing b) (a : GaussianDirectPositions b) :
    gaussianWordPositionLabel b e a.val = a := by
  simp only [gaussianWordPositionLabel, a.property, dite_true]

theorem gaussian_word_position_label_adjoint {α : Type*} (b : α → Bool)
    (e : GaussianWordPairing b) (a : GaussianDirectPositions b) :
    gaussianWordPositionLabel b e (e a).val = a := by
  simp only [gaussianWordPositionLabel, (e a).property, Bool.true_eq_false, dite_false]
  exact e.symm_apply_apply a

theorem gaussian_word_pairing_positions_distinct {α : Type*} (b : α → Bool)
    (e : GaussianWordPairing b) (a : GaussianDirectPositions b) : a.val ≠ (e a).val := by
  intro h
  have hb := congrArg b h
  rw [a.property, (e a).property] at hb
  exact Bool.noConfusion hb

theorem gaussian_word_position_label_fiber {α : Type*} (b : α → Bool)
    (e : GaussianWordPairing b) (a : GaussianDirectPositions b) (v : α) :
    gaussianWordPositionLabel b e v = a ↔ v = a.val ∨ v = (e a).val := by
  constructor
  · intro hLabel
    by_cases hv : b v = false
    · left
      have hDirect : gaussianWordPositionLabel b e v = (⟨v, hv⟩ : GaussianDirectPositions b) :=
        gaussian_word_position_label_direct b e ⟨v, hv⟩
      exact congrArg Subtype.val (hDirect.symm.trans hLabel)
    · right
      have hvTrue : b v = true := Bool.eq_true_of_not_eq_false hv
      have hAdjoint : e (gaussianWordPositionLabel b e v) =
          (⟨v, hvTrue⟩ : GaussianAdjointPositions b) := by
        rw [gaussianWordPositionLabel, dif_neg hv, Equiv.apply_symm_apply]
      exact congrArg Subtype.val (hAdjoint.symm.trans (congrArg e hLabel))
  · rintro (rfl | rfl)
    · exact gaussian_word_position_label_direct b e a
    · exact gaussian_word_position_label_adjoint b e a

def gaussianWordPositionEdge {α : Type*} (b : α → Bool) (ρ : Equiv.Perm α)
    (e : GaussianWordPairing b) (v : α) :
    Sym2 (Quotient (Relation.EqvGen.setoid (pairedWalkRelation ρ
      (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val)))) :=
  Sym2.mk (pairedWalkClass ρ (fun a : GaussianDirectPositions b => a.val)
      (fun a => (e a).val) v,
    pairedWalkClass ρ (fun a : GaussianDirectPositions b => a.val)
      (fun a => (e a).val) (ρ v))

theorem gaussian_word_position_edge_adjoint {α : Type*} (b : α → Bool)
    (ρ : Equiv.Perm α) (e : GaussianWordPairing b) (a : GaussianDirectPositions b) :
    gaussianWordPositionEdge b ρ e (e a).val = gaussianWordPositionEdge b ρ e a.val := by
  rw [gaussianWordPositionEdge, gaussianWordPositionEdge,
    ← paired_walk_class_start ρ (fun a : GaussianDirectPositions b => a.val)
      (fun a => (e a).val) a,
    ← paired_walk_class_end ρ (fun a : GaussianDirectPositions b => a.val)
      (fun a => (e a).val) a]
  exact Sym2.eq_swap

theorem gaussian_word_position_edge_eq_label_edge {α : Type*} (b : α → Bool)
    (ρ : Equiv.Perm α) (e : GaussianWordPairing b) (v : α) :
    gaussianWordPositionEdge b ρ e v =
      gaussianWordPositionEdge b ρ e (gaussianWordPositionLabel b e v).val := by
  have h := (gaussian_word_position_label_fiber b e (gaussianWordPositionLabel b e v) v).mp rfl
  rcases h with h | h
  · exact congrArg (gaussianWordPositionEdge b ρ e) h
  · exact (congrArg (gaussianWordPositionEdge b ρ e) h).trans
      (gaussian_word_position_edge_adjoint b ρ e _)

end CircularLaw
