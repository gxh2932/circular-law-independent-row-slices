import CircularLaw.FiniteLabeledTrees
import CircularLaw.GaussianWordEdgeLabels
import CircularLaw.GaussianWordMeanLimits

/-!
# Every leading Gaussian word pairing is a tree with distinct edge labels

This extends the alternating Gram-word characterization to arbitrary
direct/adjoint order. The maximal quotient exponent excludes loops and
repeated unordered edges. Consequently the two occurrences of each
actual graph edge are precisely its matched word positions.
-/

noncomputable section
open Classical

namespace CircularLaw

abbrev gaussianWordPairingGraph {α : Type*} (b : α → Bool) (ρ : Equiv.Perm α)
    (e : GaussianWordPairing b) :=
  pairedWalkGraph ρ (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val)

theorem gaussian_word_pairing_graph_connected {α : Type*} [Nonempty α]
    (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b)
    (hOrbit : ∀ v w, ρ.SameCycle v w) : (gaussianWordPairingGraph b ρ e).Connected :=
  paired_walk_graph_connected ρ _ _ (gaussian_word_pairing_covers_positions b e) hOrbit

theorem gaussian_word_leading_pairing_tree {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b)
    (hOrbit : ∀ v w, ρ.SameCycle v w)
    (hLeading : gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1) :
    (gaussianWordPairingGraph b ρ e).IsTree :=
  finite_labeled_maximal_vertex_tree _ _ (gaussian_word_pairing_graph_connected b ρ e hOrbit) hLeading

theorem gaussian_word_leading_pairing_nonloop {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b)
    (hOrbit : ∀ v w, ρ.SameCycle v w)
    (hLeading : gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1)
    (a : GaussianDirectPositions b) :
    pairedWalkClass ρ (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) a.val ≠
      pairedWalkClass ρ (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) (ρ a.val) :=
  finite_labeled_maximal_vertex_nonloop _ _
    (gaussian_word_pairing_graph_connected b ρ e hOrbit) hLeading a

theorem gaussian_word_leading_direct_edge_injective {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b)
    (hOrbit : ∀ v w, ρ.SameCycle v w)
    (hLeading : gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1) :
    Function.Injective (fun a : GaussianDirectPositions b => gaussianWordPositionEdge b ρ e a.val) := by
  intro a c hEdge
  exact finite_labeled_maximal_vertex_label_eq_of_edge_eq _ _
    (gaussian_word_pairing_graph_connected b ρ e hOrbit) hLeading hEdge

theorem gaussian_word_leading_position_edge_eq_iff {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b)
    (hOrbit : ∀ v w, ρ.SameCycle v w)
    (hLeading : gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1)
    (v w : α) :
    gaussianWordPositionEdge b ρ e v = gaussianWordPositionEdge b ρ e w ↔
      gaussianWordPositionLabel b e v = gaussianWordPositionLabel b e w := by
  rw [gaussian_word_position_edge_eq_label_edge b ρ e v,
    gaussian_word_position_edge_eq_label_edge b ρ e w]
  exact (gaussian_word_leading_direct_edge_injective b ρ e hOrbit hLeading).eq_iff

theorem gaussian_word_leading_position_edge_fiber {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b)
    (hOrbit : ∀ v w, ρ.SameCycle v w)
    (hLeading : gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1)
    (a : GaussianDirectPositions b) (v : α) :
    gaussianWordPositionEdge b ρ e v = gaussianWordPositionEdge b ρ e a.val ↔
      v = a.val ∨ v = (e a).val := by
  rw [gaussian_word_leading_position_edge_eq_iff b ρ e hOrbit hLeading,
    gaussian_word_position_label_direct, gaussian_word_position_label_fiber]

theorem gaussian_word_leading_position_adj {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b)
    (hOrbit : ∀ v w, ρ.SameCycle v w)
    (hLeading : gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1)
    (v : α) :
    (gaussianWordPairingGraph b ρ e).Adj
      (pairedWalkClass ρ (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) v)
      (pairedWalkClass ρ (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) (ρ v)) := by
  rcases gaussian_word_pairing_covers_positions b e v with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact ⟨gaussian_word_leading_pairing_nonloop b ρ e hOrbit hLeading a,
      a, Or.inl ⟨rfl, rfl⟩⟩
  · rw [← paired_walk_class_start ρ (fun a : GaussianDirectPositions b => a.val)
      (fun a => (e a).val) a,
      ← paired_walk_class_end ρ (fun a : GaussianDirectPositions b => a.val)
      (fun a => (e a).val) a]
    exact ⟨(gaussian_word_leading_pairing_nonloop b ρ e hOrbit hLeading a).symm,
      a, Or.inr ⟨rfl, rfl⟩⟩

theorem gaussian_word_leading_iff_tree_labels {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b)
    (hOrbit : ∀ v w, ρ.SameCycle v w) :
    gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1 ↔
      ∃ hNoLoops : ∀ a : GaussianDirectPositions b,
        pairedWalkClass ρ (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) a.val ≠
          pairedWalkClass ρ (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) (ρ a.val),
        (gaussianWordPairingGraph b ρ e).IsTree ∧
          Function.Bijective (finiteLabeledTotalEdge
            (fun a : GaussianDirectPositions b => pairedWalkClass ρ
              (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) a.val)
            (fun a => pairedWalkClass ρ (fun a : GaussianDirectPositions b => a.val)
              (fun a => (e a).val) (ρ a.val)) hNoLoops) :=
  finite_labeled_maximal_vertex_iff_tree_labels _ _
    (gaussian_word_pairing_graph_connected b ρ e hOrbit)

end CircularLaw
