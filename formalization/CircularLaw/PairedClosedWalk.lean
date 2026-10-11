import CircularLaw.FiniteRelationColorings
import CircularLaw.FiniteLabeledGraph
import CircularLaw.GaussianMomentCycleBound

/-!
# Vertex identifications in paired closed walks

A direct edge at `p a` is matched with a conjugate edge at `q a`.
Reversing the latter identifies both endpoints. Every position is a
direct or conjugate edge, so the quotient graph follows the entire
cyclic walk using at most one edge per pair. Its number of free vertex
classes is therefore at most the number of pairs plus one.
-/

noncomputable section
open Classical

namespace CircularLaw

def pairedWalkRelation {α P : Type*} (ρ : Equiv.Perm α) (p q : P → α)
    (v w : α) : Prop :=
  ∃ a, (v = p a ∧ w = ρ (q a)) ∨ (v = ρ (p a) ∧ w = q a)

def pairedWalkClass {α P : Type*} (ρ : Equiv.Perm α) (p q : P → α) (v : α) :
    Quotient (Relation.EqvGen.setoid (pairedWalkRelation ρ p q)) := Quotient.mk _ v

theorem paired_walk_class_start {α P : Type*} (ρ : Equiv.Perm α) (p q : P → α)
    (a : P) : pairedWalkClass ρ p q (p a) = pairedWalkClass ρ p q (ρ (q a)) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ ⟨a, Or.inl ⟨rfl, rfl⟩⟩

theorem paired_walk_class_end {α P : Type*} (ρ : Equiv.Perm α) (p q : P → α)
    (a : P) : pairedWalkClass ρ p q (ρ (p a)) = pairedWalkClass ρ p q (q a) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ ⟨a, Or.inr ⟨rfl, rfl⟩⟩

def pairedWalkGraph {α P : Type*} (ρ : Equiv.Perm α) (p q : P → α) :=
  finiteLabeledGraph (fun a => pairedWalkClass ρ p q (p a))
    (fun a => pairedWalkClass ρ p q (ρ (p a)))

theorem paired_walk_graph_successor_reachable {α P : Type*} (ρ : Equiv.Perm α)
    (p q : P → α) (hCover : ∀ v, (∃ a, p a = v) ∨ ∃ a, q a = v) (v : α) :
    (pairedWalkGraph ρ p q).Reachable (pairedWalkClass ρ p q v)
      (pairedWalkClass ρ p q (ρ v)) := by
  rcases hCover v with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact finite_labeled_endpoints_reachable _ _ a
  · rw [← paired_walk_class_start ρ p q a, ← paired_walk_class_end ρ p q a]
    exact (finite_labeled_endpoints_reachable _ _ a).symm

theorem paired_walk_graph_same_cycle_reachable {α P : Type*} (ρ : Equiv.Perm α)
    (p q : P → α) (hCover : ∀ v, (∃ a, p a = v) ∨ ∃ a, q a = v)
    {v w : α} (hvw : ρ.SameCycle v w) :
    (pairedWalkGraph ρ p q).Reachable (pairedWalkClass ρ p q v)
      (pairedWalkClass ρ p q w) := by
  have hPow (m : ℤ) (x : α) :
      (pairedWalkGraph ρ p q).Reachable (pairedWalkClass ρ p q x)
        (pairedWalkClass ρ p q ((ρ ^ m) x)) := by
    induction m using Int.induction_on generalizing x with
    | zero => simp
    | succ m ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply]
      exact (paired_walk_graph_successor_reachable ρ p q hCover x).trans (ih (ρ x))
    | pred m ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply]
      have hBack : (pairedWalkGraph ρ p q).Reachable (pairedWalkClass ρ p q x)
          (pairedWalkClass ρ p q (ρ⁻¹ x)) := by
        simpa using (paired_walk_graph_successor_reachable ρ p q hCover (ρ.symm x)).symm
      exact hBack.trans (ih (ρ⁻¹ x))
  obtain ⟨m, rfl⟩ := hvw
  exact hPow m v

theorem paired_walk_graph_connected {α P : Type*} [Nonempty α] (ρ : Equiv.Perm α)
    (p q : P → α) (hCover : ∀ v, (∃ a, p a = v) ∨ ∃ a, q a = v)
    (hOrbit : ∀ v w, ρ.SameCycle v w) : (pairedWalkGraph ρ p q).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  obtain ⟨v₀⟩ := ‹Nonempty α›
  refine ⟨pairedWalkClass ρ p q v₀, ?_⟩
  intro c
  induction c using Quotient.inductionOn with
  | h w => exact paired_walk_graph_same_cycle_reachable ρ p q hCover (hOrbit v₀ w)

theorem paired_walk_class_count_bound {α P : Type*} [Fintype α] [Nonempty α]
    [Fintype P] (ρ : Equiv.Perm α) (p q : P → α)
    (hCover : ∀ v, (∃ a, p a = v) ∨ ∃ a, q a = v)
    (hOrbit : ∀ v w, ρ.SameCycle v w) :
    relationClassCount (pairedWalkRelation ρ p q) ≤ Fintype.card P + 1 := by
  exact finite_labeled_vertex_card_bound _ _ (paired_walk_graph_connected ρ p q hCover hOrbit)

theorem paired_walk_coloring_iff {α P β : Type*} (ρ : Equiv.Perm α) (p q : P → α)
    (f : α → β) :
    (∀ v w, pairedWalkRelation ρ p q v w → f v = f w) ↔
      ∀ a, f (p a) = f (ρ (q a)) ∧ f (ρ (p a)) = f (q a) := by
  constructor
  · intro h a
    exact ⟨h _ _ ⟨a, Or.inl ⟨rfl, rfl⟩⟩, h _ _ ⟨a, Or.inr ⟨rfl, rfl⟩⟩⟩
  · rintro h v w ⟨a, hRel⟩
    rcases hRel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (h a).1
    · exact (h a).2

theorem paired_walk_coloring_card {α P : Type*} [Fintype α] [DecidableEq α]
    (ρ : Equiv.Perm α) (p q : P → α) (n : ℕ) :
    Fintype.card {f : α → Fin n //
      ∀ a, f (p a) = f (ρ (q a)) ∧ f (ρ (p a)) = f (q a)} =
      n ^ relationClassCount (pairedWalkRelation ρ p q) := by
  let e : {f : α → Fin n //
      ∀ a, f (p a) = f (ρ (q a)) ∧ f (ρ (p a)) = f (q a)} ≃
      {f : α → Fin n // ∀ v w, pairedWalkRelation ρ p q v w → f v = f w} :=
    Equiv.subtypeEquivRight (fun f => (paired_walk_coloring_iff ρ p q f).symm)
  exact (Fintype.card_congr e).trans (relation_fin_coloring_card _ n)

end CircularLaw
