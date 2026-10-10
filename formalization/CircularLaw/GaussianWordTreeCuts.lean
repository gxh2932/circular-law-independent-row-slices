import CircularLaw.GaussianWordLeadingTrees
import CircularLaw.TreeEdgeCuts
import CircularLaw.FiniteCircularCuts

/-!
# Leading Gaussian word matchings cannot cross

Deleting one leading tree edge gives a side predicate on the actual word
positions. It switches exactly at that pair's direct and adjoint positions
and is constant at every other successor. The finite circular cut identifies
it explicitly. Every other matched pair has both positions on the same
side, proving the noncrossing condition without assuming it.
-/

noncomputable section
open Classical

namespace CircularLaw

abbrev GaussianWordVertexClass {α : Type*} (b : α → Bool) (ρ : Equiv.Perm α)
    (e : GaussianWordPairing b) :=
  Quotient (Relation.EqvGen.setoid (pairedWalkRelation ρ
    (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val)))

abbrev gaussianWordVertex {α : Type*} (b : α → Bool) (ρ : Equiv.Perm α)
    (e : GaussianWordPairing b) (v : α) : GaussianWordVertexClass b ρ e :=
  pairedWalkClass ρ (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) v

def gaussianWordTreeSide {α : Type*} (b : α → Bool) (ρ : Equiv.Perm α)
    (e : GaussianWordPairing b) (a : GaussianDirectPositions b) (v : α) : Prop :=
  treeEdgeSide (gaussianWordPairingGraph b ρ e)
    (gaussianWordVertex b ρ e a.val) (gaussianWordVertex b ρ e (ρ a.val))
    (gaussianWordVertex b ρ e v)

theorem gaussian_word_tree_side_direct {α : Type*} (b : α → Bool) (ρ : Equiv.Perm α)
    (e : GaussianWordPairing b) (a : GaussianDirectPositions b) :
    gaussianWordTreeSide b ρ e a a.val := tree_edge_side_start _ _ _

theorem gaussian_word_tree_side_after_direct {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b)
    (hOrbit : ∀ v w, ρ.SameCycle v w)
    (hLeading : gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1)
    (a : GaussianDirectPositions b) : ¬gaussianWordTreeSide b ρ e a (ρ a.val) :=
  tree_edge_side_not_end _ (tree_edge_is_bridge _
    (gaussian_word_leading_pairing_tree b ρ e hOrbit hLeading)
    (gaussian_word_leading_position_adj b ρ e hOrbit hLeading a.val))

theorem gaussian_word_tree_side_adjoint {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b)
    (hOrbit : ∀ v w, ρ.SameCycle v w)
    (hLeading : gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1)
    (a : GaussianDirectPositions b) : ¬gaussianWordTreeSide b ρ e a (e a).val := by
  change ¬treeEdgeSide _ _ _ (pairedWalkClass ρ
    (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) (e a).val)
  rw [← paired_walk_class_end ρ (fun a : GaussianDirectPositions b => a.val)
    (fun a => (e a).val) a]
  exact gaussian_word_tree_side_after_direct b ρ e hOrbit hLeading a

theorem gaussian_word_tree_side_after_adjoint {α : Type*} (b : α → Bool)
    (ρ : Equiv.Perm α) (e : GaussianWordPairing b) (a : GaussianDirectPositions b) :
    gaussianWordTreeSide b ρ e a (ρ (e a).val) := by
  change treeEdgeSide _ _ _ (pairedWalkClass ρ
    (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) (ρ (e a).val))
  rw [← paired_walk_class_start ρ (fun a : GaussianDirectPositions b => a.val)
    (fun a => (e a).val) a]
  exact gaussian_word_tree_side_direct b ρ e a

theorem gaussian_word_tree_side_other_successor {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b)
    (hOrbit : ∀ v w, ρ.SameCycle v w)
    (hLeading : gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1)
    (a : GaussianDirectPositions b) (v : α) (hDirect : v ≠ a.val) (hAdjoint : v ≠ (e a).val) :
    gaussianWordTreeSide b ρ e a (ρ v) ↔ gaussianWordTreeSide b ρ e a v := by
  symm
  apply tree_edge_side_of_other_adj _ _ _
    (gaussian_word_leading_position_adj b ρ e hOrbit hLeading v)
  change gaussianWordPositionEdge b ρ e v ≠ gaussianWordPositionEdge b ρ e a.val
  intro h
  rcases (gaussian_word_leading_position_edge_fiber b ρ e hOrbit hLeading a v).mp h with h | h
  · exact hDirect h
  · exact hAdjoint h

theorem gaussian_word_tree_side_other_pair {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b)
    (hOrbit : ∀ v w, ρ.SameCycle v w)
    (hLeading : gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1)
    (a c : GaussianDirectPositions b) (hca : c ≠ a) :
    gaussianWordTreeSide b ρ e a c.val ↔ gaussianWordTreeSide b ρ e a (e c).val := by
  have hSide := tree_edge_side_of_other_adj (gaussianWordPairingGraph b ρ e)
    (gaussianWordVertex b ρ e a.val) (gaussianWordVertex b ρ e (ρ a.val))
    (gaussian_word_leading_position_adj b ρ e hOrbit hLeading c.val)
    (fun h => hca (gaussian_word_leading_direct_edge_injective b ρ e hOrbit hLeading h))
  change treeEdgeSide _ _ _ (pairedWalkClass ρ
      (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) c.val) ↔
    treeEdgeSide _ _ _ (pairedWalkClass ρ
      (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) (ρ c.val)) at hSide
  rw [paired_walk_class_end ρ (fun a : GaussianDirectPositions b => a.val)
    (fun a => (e a).val) c] at hSide
  exact hSide

theorem gaussian_word_leading_cut_interval (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b)
    (hLeading : gaussianWordVertexExponent b (finRotate (k + 1)) e =
      Fintype.card (GaussianDirectPositions b) + 1)
    (a : GaussianDirectPositions b) (v : Fin (k + 1)) :
    gaussianWordTreeSide b (finRotate (k + 1)) e a v ↔
      finiteCircularCut a.val (e a).val v :=
  finite_circular_cut_eq_of_two_switches a.val (e a).val
    (gaussian_word_pairing_positions_distinct b e a) _
    (gaussian_word_tree_side_direct b _ e a)
    (gaussian_word_tree_side_adjoint b _ e (fin_rotate_same_cycle k) hLeading a)
    (gaussian_word_tree_side_after_direct b _ e (fin_rotate_same_cycle k) hLeading a)
    (gaussian_word_tree_side_after_adjoint b _ e a)
    (gaussian_word_tree_side_other_successor b _ e (fin_rotate_same_cycle k) hLeading a) v

def GaussianWordNoncrossing {n : ℕ} (b : Fin n → Bool) (e : GaussianWordPairing b) : Prop :=
  ∀ a c : GaussianDirectPositions b, c ≠ a →
    (finiteCircularCut a.val (e a).val c.val ↔ finiteCircularCut a.val (e a).val (e c).val)

theorem gaussian_word_leading_noncrossing (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b)
    (hLeading : gaussianWordVertexExponent b (finRotate (k + 1)) e =
      Fintype.card (GaussianDirectPositions b) + 1) : GaussianWordNoncrossing b e := by
  intro a c hca
  rw [← gaussian_word_leading_cut_interval k b e hLeading a c.val,
    ← gaussian_word_leading_cut_interval k b e hLeading a (e c).val]
  exact gaussian_word_tree_side_other_pair b _ e (fin_rotate_same_cycle k) hLeading a c hca

theorem gaussian_word_leading_no_ordered_crossing (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b)
    (hLeading : gaussianWordVertexExponent b (finRotate (k + 1)) e =
      Fintype.card (GaussianDirectPositions b) + 1)
    (a c : GaussianDirectPositions b) (hac : a.val < c.val) (hcqa : c.val < (e a).val)
    (haqc : (e a).val < (e c).val) : False := by
  have hca : c ≠ a := fun h => (ne_of_gt hac) (congrArg Subtype.val h)
  have hCut := gaussian_word_leading_noncrossing k b e hLeading a c hca
  simp only [finiteCircularCut, if_pos (hac.trans hcqa)] at hCut
  have hInside : ¬(c.val ≤ a.val ∨ (e a).val < c.val) := by omega
  have hOutside : (e c).val ≤ a.val ∨ (e a).val < (e c).val := Or.inr haqc
  exact hInside (hCut.mpr hOutside)

end CircularLaw
