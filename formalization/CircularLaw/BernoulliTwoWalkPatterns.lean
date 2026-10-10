import CircularLaw.BernoulliWordCovarianceWeights
import CircularLaw.ClosedTwoWalkGraph

/-!
# Exact joint Bernoulli walk patterns and their connected-graph bound

Both traces are labeled by one function on the disjoint union of their
positions. Its exact kernel supplies the canonical quotient entry words.
Injective relabeling preserves the joint covariance weight. Disjoint
entry supports cancel exactly; when entries are shared, the quotient
graph is connected and has at most one more vertex than entry labels.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal

namespace CircularLaw

abbrev BernoulliTwoWalkPositions (k l : ℕ) := Fin (k + 1) ⊕ Fin (l + 1)

def bernoulliTwoWalkRotate (k l : ℕ) : Equiv.Perm (BernoulliTwoWalkPositions k l) :=
  Equiv.sumCongr (finRotate (k + 1)) (finRotate (l + 1))

def bernoulliTwoPatternLeftWord {k l : ℕ} (b : Fin (k + 1) → Bool)
    (c : Fin (l + 1) → Bool) (s : Setoid (BernoulliTwoWalkPositions k l)) :
    List (Quotient s × Quotient s) :=
  List.ofFn (fun a => orientedClosedWalkEntry (bernoulliTwoWalkRotate k l)
    (Sum.elim b c) (Quotient.mk s) (Sum.inl a))

def bernoulliTwoPatternRightWord {k l : ℕ} (b : Fin (k + 1) → Bool)
    (c : Fin (l + 1) → Bool) (s : Setoid (BernoulliTwoWalkPositions k l)) :
    List (Quotient s × Quotient s) :=
  List.ofFn (fun a => orientedClosedWalkEntry (bernoulliTwoWalkRotate k l)
    (Sum.elim b c) (Quotient.mk s) (Sum.inr a))

def bernoulliTwoPatternJointWord {k l : ℕ} (b : Fin (k + 1) → Bool)
    (c : Fin (l + 1) → Bool) (s : Setoid (BernoulliTwoWalkPositions k l)) :
    List (Quotient s × Quotient s) :=
  bernoulliTwoPatternLeftWord b c s ++ bernoulliTwoPatternRightWord b c s

def bernoulliTwoPatternVertexCount {k l : ℕ} (s : Setoid (BernoulliTwoWalkPositions k l)) : ℕ :=
  Nat.card (Quotient s)

def bernoulliTwoPatternEntryCount {k l : ℕ} (b : Fin (k + 1) → Bool)
    (c : Fin (l + 1) → Bool) (s : Setoid (BernoulliTwoWalkPositions k l)) : ℕ :=
  (bernoulliTwoPatternJointWord b c s).toFinset.card

local instance bernoulliTwoPatternQuotientBEq {α : Type*} (s : Setoid α) :
    BEq (Quotient s × Quotient s) := instBEqOfDecidableEq

def BernoulliTwoPatternSurvives {k l : ℕ} (b : Fin (k + 1) → Bool)
    (c : Fin (l + 1) → Bool) (s : Setoid (BernoulliTwoWalkPositions k l)) : Prop :=
  ∀ e, (bernoulliTwoPatternJointWord b c s).count e ≠ 1

def BernoulliTwoPatternSharesEntry {k l : ℕ} (b : Fin (k + 1) → Bool)
    (c : Fin (l + 1) → Bool) (s : Setoid (BernoulliTwoWalkPositions k l)) : Prop :=
  ¬ Disjoint (bernoulliTwoPatternLeftWord b c s).toFinset
    (bernoulliTwoPatternRightWord b c s).toFinset

def bernoulliTwoPatternCovarianceWeight {k l : ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) : ℝ :=
  bernoulliWordCovarianceWeight p hp (bernoulliTwoPatternLeftWord b c s)
    (bernoulliTwoPatternRightWord b c s)

theorem bernoulli_two_pattern_joint_word_length {k l : ℕ} (b : Fin (k + 1) → Bool)
    (c : Fin (l + 1) → Bool) (s : Setoid (BernoulliTwoWalkPositions k l)) :
    (bernoulliTwoPatternJointWord b c s).length = k + l + 2 := by
  simp only [bernoulliTwoPatternJointWord, List.length_append,
    bernoulliTwoPatternLeftWord, bernoulliTwoPatternRightWord, List.length_ofFn]
  omega

theorem bernoulli_two_pattern_left_kernel_map {n k l : ℕ} (b : Fin (k + 1) → Bool)
    (c : Fin (l + 1) → Bool) (s : Setoid (BernoulliTwoWalkPositions k l))
    (v : BernoulliTwoWalkPositions k l → Fin n) (hKernel : ∀ a t, v a = v t ↔ s a t) :
    bernoulliWalkEntries b (fun a => v (Sum.inl a)) = (bernoulliTwoPatternLeftWord b c s).map
      (Prod.map ((fixedKernelColoringsEquiv s ⟨v, hKernel⟩) : Quotient s → Fin n)
        ((fixedKernelColoringsEquiv s ⟨v, hKernel⟩) : Quotient s → Fin n)) := by
  rw [bernoulliWalkEntries, bernoulliTwoPatternLeftWord, List.map_ofFn]
  apply congrArg List.ofFn
  funext a
  cases h : b a <;>
    simp [orientedClosedWalkEntry, bernoulliTwoWalkRotate, h, fixedKernelColoringsEquiv]

theorem bernoulli_two_pattern_right_kernel_map {n k l : ℕ} (b : Fin (k + 1) → Bool)
    (c : Fin (l + 1) → Bool) (s : Setoid (BernoulliTwoWalkPositions k l))
    (v : BernoulliTwoWalkPositions k l → Fin n) (hKernel : ∀ a t, v a = v t ↔ s a t) :
    bernoulliWalkEntries c (fun a => v (Sum.inr a)) = (bernoulliTwoPatternRightWord b c s).map
      (Prod.map ((fixedKernelColoringsEquiv s ⟨v, hKernel⟩) : Quotient s → Fin n)
        ((fixedKernelColoringsEquiv s ⟨v, hKernel⟩) : Quotient s → Fin n)) := by
  rw [bernoulliWalkEntries, bernoulliTwoPatternRightWord, List.map_ofFn]
  apply congrArg List.ofFn
  funext a
  cases h : c a <;>
    simp [orientedClosedWalkEntry, bernoulliTwoWalkRotate, h, fixedKernelColoringsEquiv]

theorem bernoulli_two_walk_covariance_constant_on_kernel {n k l : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (v : BernoulliTwoWalkPositions k l → Fin n)
    (hKernel : ∀ a t, v a = v t ↔ s a t) :
    bernoulliWordCovarianceWeight p hp (bernoulliWalkEntries b (fun a => v (Sum.inl a)))
      (bernoulliWalkEntries c (fun a => v (Sum.inr a))) =
        bernoulliTwoPatternCovarianceWeight p hp b c s := by
  rw [bernoulli_two_pattern_left_kernel_map b c s v hKernel,
    bernoulli_two_pattern_right_kernel_map b c s v hKernel]
  unfold bernoulliTwoPatternCovarianceWeight
  apply bernoulli_word_covariance_weight_map
  intro x y h
  apply Prod.ext
  · exact (fixedKernelColoringsEquiv s ⟨v, hKernel⟩).injective (congrArg Prod.fst h)
  · exact (fixedKernelColoringsEquiv s ⟨v, hKernel⟩).injective (congrArg Prod.snd h)

theorem bernoulli_two_pattern_no_shared_covariance_zero {k l : ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (hNot : ¬ BernoulliTwoPatternSharesEntry b c s) :
    bernoulliTwoPatternCovarianceWeight p hp b c s = 0 := by
  apply bernoulli_word_covariance_weight_disjoint_zero
  exact not_not.mp hNot

theorem bernoulli_two_pattern_nonsurviving_covariance_zero {k l : ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (hNot : ¬ BernoulliTwoPatternSurvives b c s) :
    bernoulliTwoPatternCovarianceWeight p hp b c s = 0 := by
  unfold BernoulliTwoPatternSurvives at hNot
  push_neg at hNot
  obtain ⟨e, he⟩ := hNot
  exact bernoulli_word_covariance_weight_singleton_zero p hp _ _ e he

theorem bernoulli_two_pattern_covariance_abs_bound {k l : ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (hSurvive : BernoulliTwoPatternSurvives b c s) :
    |bernoulliTwoPatternCovarianceWeight p hp b c s| ≤
      2 * (p : ℝ) ^ bernoulliTwoPatternEntryCount b c s :=
  bernoulli_word_covariance_weight_abs_bound p hp _ _ hSurvive

theorem bernoulli_two_pattern_surviving_entry_bound {k l : ℕ} (b : Fin (k + 1) → Bool)
    (c : Fin (l + 1) → Bool) (s : Setoid (BernoulliTwoWalkPositions k l))
    (hSurvive : BernoulliTwoPatternSurvives b c s) :
    2 * bernoulliTwoPatternEntryCount b c s ≤ k + l + 2 := by
  simpa only [bernoulliTwoPatternEntryCount, bernoulli_two_pattern_joint_word_length] using
    bernoulli_centered_entry_word_distinct_count_bound (bernoulliTwoPatternJointWord b c s) hSurvive

theorem bernoulli_two_pattern_quotient_range_card {k l : ℕ}
    (s : Setoid (BernoulliTwoWalkPositions k l)) :
    Nat.card (Set.range (Quotient.mk s)) = bernoulliTwoPatternVertexCount s := by
  have hRange : Set.range (Quotient.mk s) = Set.univ :=
    Set.range_eq_univ.mpr Quotient.mk_surjective
  simp only [hRange, Nat.card_eq_fintype_card, Fintype.card_setUniv,
    bernoulliTwoPatternVertexCount]

theorem bernoulli_two_pattern_entry_range_card {k l : ℕ} (b : Fin (k + 1) → Bool)
    (c : Fin (l + 1) → Bool) (s : Setoid (BernoulliTwoWalkPositions k l)) :
    Nat.card (Set.range (orientedClosedWalkEntry (bernoulliTwoWalkRotate k l)
      (Sum.elim b c) (Quotient.mk s))) = bernoulliTwoPatternEntryCount b c s := by
  let e : Set.range (orientedClosedWalkEntry (bernoulliTwoWalkRotate k l)
      (Sum.elim b c) (Quotient.mk s)) ≃ (bernoulliTwoPatternJointWord b c s).toFinset :=
    Equiv.subtypeEquivRight (fun x => by
      simp only [bernoulliTwoPatternJointWord, bernoulliTwoPatternLeftWord,
        bernoulliTwoPatternRightWord, List.mem_toFinset, List.mem_append, List.mem_ofFn', Set.mem_range]
      constructor
      · rintro ⟨a, ha⟩
        cases a with
        | inl a => exact Or.inl ⟨a, ha⟩
        | inr a => exact Or.inr ⟨a, ha⟩
      · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
        · exact ⟨Sum.inl a, ha⟩
        · exact ⟨Sum.inr a, ha⟩)
  exact (Nat.card_congr e).trans (by
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe, bernoulliTwoPatternEntryCount])

theorem bernoulli_two_pattern_shared_entry_vertex_bound {k l : ℕ}
    (b : Fin (k + 1) → Bool) (c : Fin (l + 1) → Bool)
    (s : Setoid (BernoulliTwoWalkPositions k l)) (hShared : BernoulliTwoPatternSharesEntry b c s) :
    bernoulliTwoPatternVertexCount s ≤ bernoulliTwoPatternEntryCount b c s + 1 := by
  obtain ⟨e, heL, heR⟩ := Finset.not_disjoint_iff.mp hShared
  obtain ⟨a, ha⟩ : ∃ a, orientedClosedWalkEntry (bernoulliTwoWalkRotate k l)
      (Sum.elim b c) (Quotient.mk s) (Sum.inl a) = e := by
    simpa only [bernoulliTwoPatternLeftWord, List.mem_toFinset, List.mem_ofFn'] using heL
  obtain ⟨t, ht⟩ : ∃ t, orientedClosedWalkEntry (bernoulliTwoWalkRotate k l)
      (Sum.elim b c) (Quotient.mk s) (Sum.inr t) = e := by
    simpa only [bernoulliTwoPatternRightWord, List.mem_toFinset, List.mem_ofFn'] using heR
  have h := closed_two_walk_shared_entry_vertex_bound (finRotate (k + 1))
    (finRotate (l + 1)) (Sum.elim b c) (Quotient.mk s)
    (fin_rotate_same_cycle k) (fin_rotate_same_cycle l) ⟨a, t, ha.trans ht.symm⟩
  change Nat.card (Set.range (Quotient.mk s)) ≤
    Nat.card (Set.range (orientedClosedWalkEntry (bernoulliTwoWalkRotate k l)
      (Sum.elim b c) (Quotient.mk s))) + 1 at h
  rwa [bernoulli_two_pattern_quotient_range_card, bernoulli_two_pattern_entry_range_card] at h

end CircularLaw
