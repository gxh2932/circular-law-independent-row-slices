import CircularLaw.WitnessSliceCount

/-!
# Exact finite disjoint unions

Mutually exclusive events have an exact sum of counting probabilities.
This identifies the singleton witness probability by its selected
coordinate, rather than estimating an overlapping union.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem uniformProbability_finset_exists_eq {α ι : Type*} [Fintype α]
    (T : Finset ι) (E : ι → α → Prop)
    (hUnique : ∀ a i, i ∈ T → ∀ j, j ∈ T → E i a → E j a → i = j) :
    uniformProbability (fun a => ∃ i ∈ T, E i a) = ∑ i ∈ T, uniformProbability (E i) := by
  have hPoint (a : α) : (if ∃ i ∈ T, E i a then (1 : ℝ) else 0) =
      ∑ i ∈ T, if E i a then (1 : ℝ) else 0 := by
    have hCard : ((T.filter (fun i => E i a)).card : ℝ) =
        ∑ i ∈ T, if E i a then (1 : ℝ) else 0 := by
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [← hCard]
    by_cases h : ∃ i ∈ T, E i a
    · obtain ⟨i, hi, hE⟩ := h
      have hFilter : T.filter (fun i => E i a) = {i} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro hj
          exact hUnique a j hj.1 i hi hj.2 hE
        · intro hEq
          subst j
          exact ⟨hi, hE⟩
      have hExists : ∃ i ∈ T, E i a := ⟨i, hi, hE⟩
      simp only [if_pos hExists, hFilter, Finset.card_singleton, Nat.cast_one]
    · have hFilter : T.filter (fun i => E i a) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨hiT, hiE⟩ := Finset.mem_filter.mp hi
        exact h ⟨i, hiT, hiE⟩
      simp only [if_neg h, hFilter, Finset.card_empty, Nat.cast_zero]
  rw [← finiteMean_indicator]
  simp_rw [hPoint]
  rw [finiteMean_finset_sum]
  simp only [finiteMean_indicator]

end CircularLaw
