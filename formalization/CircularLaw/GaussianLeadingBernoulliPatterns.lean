import CircularLaw.BernoulliLeadingGaussianKernel
import CircularLaw.GaussianWordLeadingTrees

/-!
# Every leading Gaussian matching gives a Bernoulli leading pattern

Its quotient ordered entries have exactly the Gaussian position-label
fibers, hence two occurrences with opposite flags. Distinct direct labels
bijection with the ordered entries. Thus the generated vertex kernel has
the required Bernoulli maximal vertex and paired-entry counts.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

local instance gaussianLeadingPatternBEq {α : Type*} (s : Setoid α) :
    BEq (Quotient s × Quotient s) := instBEqOfDecidableEq

theorem oriented_closed_walk_entry_unordered {α V : Type*} (ρ : Equiv.Perm α)
    (b : α → Bool) (v : α → V) (a : α) :
    Sym2.mk (orientedClosedWalkEntry ρ b v a) = Sym2.mk (v a, v (ρ a)) := by
  cases h : b a <;> simp [orientedClosedWalkEntry, h]

theorem gaussian_pairing_oriented_entry_eq_label {α : Type*} (b : α → Bool)
    (ρ : Equiv.Perm α) (e : GaussianWordPairing b) (v : α) :
    orientedClosedWalkEntry ρ b (pairedWalkClass ρ
      (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val)) v =
      (pairedWalkClass ρ (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val)
          (gaussianWordPositionLabel b e v).val,
        pairedWalkClass ρ (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val)
          (ρ (gaussianWordPositionLabel b e v).val)) := by
  rcases gaussian_word_pairing_covers_positions b e v with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [gaussian_word_position_label_direct]
    simp only [orientedClosedWalkEntry, a.property, Bool.false_eq_true, if_false]
  · rw [gaussian_word_position_label_adjoint]
    simp only [orientedClosedWalkEntry, (e a).property, if_true]
    rw [← paired_walk_class_start ρ (fun a : GaussianDirectPositions b => a.val)
      (fun a => (e a).val) a, ← paired_walk_class_end ρ
      (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) a]

theorem gaussian_leading_oriented_entry_eq_iff_label {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α)
    (e : GaussianWordPairing b) (hOrbit : ∀ a c, ρ.SameCycle a c)
    (hLeading : gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1)
    (a c : α) :
    orientedClosedWalkEntry ρ b (Quotient.mk (gaussianWordPairingSetoid b ρ e)) a =
      orientedClosedWalkEntry ρ b (Quotient.mk (gaussianWordPairingSetoid b ρ e)) c ↔
        gaussianWordPositionLabel b e a = gaussianWordPositionLabel b e c := by
  constructor
  · intro he
    have hEdge : gaussianWordPositionEdge b ρ e a = gaussianWordPositionEdge b ρ e c := by
      change Sym2.mk (pairedWalkClass ρ _ _ a, pairedWalkClass ρ _ _ (ρ a)) =
        Sym2.mk (pairedWalkClass ρ _ _ c, pairedWalkClass ρ _ _ (ρ c))
      rw [← oriented_closed_walk_entry_unordered ρ b _ a,
        ← oriented_closed_walk_entry_unordered ρ b _ c]
      exact congrArg Sym2.mk he
    exact (gaussian_word_leading_position_edge_eq_iff b ρ e hOrbit hLeading a c).mp hEdge
  · intro hLabel
    change orientedClosedWalkEntry ρ b (pairedWalkClass ρ _ _) a =
      orientedClosedWalkEntry ρ b (pairedWalkClass ρ _ _) c
    rw [gaussian_pairing_oriented_entry_eq_label, gaussian_pairing_oriented_entry_eq_label, hLabel]

def gaussianPairingDirectEntry {α : Type*} (b : α → Bool) (ρ : Equiv.Perm α)
    (e : GaussianWordPairing b) (a : GaussianDirectPositions b) :
    Set.range (orientedClosedWalkEntry ρ b (Quotient.mk (gaussianWordPairingSetoid b ρ e))) :=
  ⟨orientedClosedWalkEntry ρ b (Quotient.mk (gaussianWordPairingSetoid b ρ e)) a.val,
    ⟨a.val, rfl⟩⟩

theorem gaussian_leading_direct_entry_bijective {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α)
    (e : GaussianWordPairing b) (hOrbit : ∀ a c, ρ.SameCycle a c)
    (hLeading : gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1) :
    Function.Bijective (gaussianPairingDirectEntry b ρ e) := by
  constructor
  · intro a c he
    have hLabel := (gaussian_leading_oriented_entry_eq_iff_label b ρ e hOrbit hLeading a.val c.val).mp
      (congrArg Subtype.val he)
    simpa only [gaussian_word_position_label_direct] using hLabel
  · rintro ⟨q, a, rfl⟩
    refine ⟨gaussianWordPositionLabel b e a, Subtype.ext ?_⟩
    apply (gaussian_leading_oriented_entry_eq_iff_label b ρ e hOrbit hLeading _ _).mpr
    exact gaussian_word_position_label_direct b e _

theorem gaussian_leading_pattern_entry_count {k : ℕ} (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b)
    (hLeading : gaussianWordVertexExponent b (finRotate (k + 1)) e =
      Fintype.card (GaussianDirectPositions b) + 1) :
    bernoulliPatternEntryCount b (gaussianWordPairingSetoid b (finRotate (k + 1)) e) =
      Fintype.card (GaussianDirectPositions b) := by
  have h := Nat.card_eq_of_bijective _
    (gaussian_leading_direct_entry_bijective b _ e (fin_rotate_same_cycle k) hLeading)
  rw [bernoulli_pattern_entry_range_card, Nat.card_eq_fintype_card] at h
  exact h.symm

theorem gaussian_leading_entry_fiber_card {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (b : α → Bool) (ρ : Equiv.Perm α)
    (e : GaussianWordPairing b) (hOrbit : ∀ a c, ρ.SameCycle a c)
    (hLeading : gaussianWordVertexExponent b ρ e = Fintype.card (GaussianDirectPositions b) + 1)
    (a : α) :
    Fintype.card {c // orientedClosedWalkEntry ρ b (Quotient.mk (gaussianWordPairingSetoid b ρ e)) c =
      orientedClosedWalkEntry ρ b (Quotient.mk (gaussianWordPairingSetoid b ρ e)) a} = 2 := by
  rw [Fintype.card_subtype]
  have hFilter : (Finset.univ.filter (fun c =>
      orientedClosedWalkEntry ρ b (Quotient.mk (gaussianWordPairingSetoid b ρ e)) c =
        orientedClosedWalkEntry ρ b (Quotient.mk (gaussianWordPairingSetoid b ρ e)) a)) =
      {(gaussianWordPositionLabel b e a).val, (e (gaussianWordPositionLabel b e a)).val} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      gaussian_leading_oriented_entry_eq_iff_label b ρ e hOrbit hLeading,
      gaussian_word_position_label_fiber, Finset.mem_insert, Finset.mem_singleton]
  rw [hFilter]
  simp [gaussian_word_pairing_positions_distinct b e (gaussianWordPositionLabel b e a)]

theorem gaussian_leading_pattern_survives {k : ℕ} (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b)
    (hLeading : gaussianWordVertexExponent b (finRotate (k + 1)) e =
      Fintype.card (GaussianDirectPositions b) + 1) :
    BernoulliSurvivingPattern b (gaussianWordPairingSetoid b (finRotate (k + 1)) e) := by
  intro q
  by_cases hMem : q ∈ bernoulliPatternEntryWord b (gaussianWordPairingSetoid b (finRotate (k + 1)) e)
  · obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hMem
    change (List.ofFn _).count _ ≠ 1
    rw [list_ofFn_count_eq_fiber_card,
      gaussian_leading_entry_fiber_card b _ e (fin_rotate_same_cycle k) hLeading a]
    norm_num
  · rw [List.count_eq_zero.mpr hMem]
    norm_num

theorem gaussian_word_pairing_positions_card {α : Type*} [Fintype α]
    (b : α → Bool) (e : GaussianWordPairing b) :
    2 * Fintype.card (GaussianDirectPositions b) = Fintype.card α := by
  let c : {a // ¬b a = false} ≃ GaussianAdjointPositions b :=
    Equiv.subtypeEquivRight (fun a => by cases b a <;> simp)
  have h : Nat.card α = Nat.card (GaussianDirectPositions b) + Nat.card {a // ¬b a = false} := by
    simpa only [Nat.card_sum] using
      Nat.card_congr (Equiv.sumCompl (fun a => b a = false)).symm
  rw [Nat.card_congr c, ← Nat.card_congr e] at h
  calc
    _ = 2 * Nat.card (GaussianDirectPositions b) := by rw [Nat.card_eq_fintype_card]
    _ = Nat.card α := by omega
    _ = _ := Nat.card_eq_fintype_card

theorem gaussian_leading_pattern_is_bernoulli_leading {k : ℕ} (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b)
    (hLeading : gaussianWordVertexExponent b (finRotate (k + 1)) e =
      Fintype.card (GaussianDirectPositions b) + 1) :
    BernoulliLeadingPattern b (gaussianWordPairingSetoid b (finRotate (k + 1)) e) := by
  refine ⟨gaussian_leading_pattern_survives b e hLeading, ?_, ?_⟩
  · rw [bernoulliPatternVertexCount, gaussian_word_pairing_quotient_card,
      gaussian_leading_pattern_entry_count b e hLeading, hLeading]
  · rw [gaussian_leading_pattern_entry_count b e hLeading]
    simpa only [Fintype.card_fin] using gaussian_word_pairing_positions_card b e

end CircularLaw
