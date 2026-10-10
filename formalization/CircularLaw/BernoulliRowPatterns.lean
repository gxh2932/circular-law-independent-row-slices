import CircularLaw.BernoulliSliceFibers

/-!
# Exact Bernoulli probabilities for selected row patterns

Only coordinates in the specified finite set are constrained. Zero and
single-one patterns retain their exact probabilities, including empty
sets and endpoint parameters.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

def BernoulliRowPattern {ι : Type*} (S : Finset ι) (b x : ι → Bool) : Prop :=
  ∀ j ∈ S, x j = b j

def BernoulliRowSingle {ι : Type*} (S : Finset ι) (j : ι) (x : ι → Bool) : Prop :=
  x j = true ∧ ∀ k ∈ S, k ≠ j → x k = false

theorem bernoulli_row_pattern_probability {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) (b : ι → Bool) :
    (bernoulliCubeLaw ι p hp).real {x | BernoulliRowPattern S b x} =
      ∏ j ∈ S, if b j = true then (p : ℝ) else 1 - (p : ℝ) := by
  have hEvent : {x : ι → Bool | BernoulliRowPattern S b x} =
      Set.univ.pi (fun j => if j ∈ S then {b j} else Set.univ) := by
    ext x
    simp only [Set.mem_setOf_eq, BernoulliRowPattern, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro hx j
      by_cases hj : j ∈ S
      · simpa only [if_pos hj, Set.mem_singleton_iff] using hx j hj
      · simp only [if_neg hj, Set.mem_univ]
    · intro hx j hj
      simpa only [if_pos hj, Set.mem_singleton_iff] using hx j
  rw [hEvent, measureReal_def, bernoulliCubeLaw, Measure.pi_pi, ENNReal.toReal_prod]
  have hFactor (j : ι) :
      (bernoulliCoordinateLaw p hp (if j ∈ S then {b j} else Set.univ)).toReal =
        if j ∈ S then (if b j = true then (p : ℝ) else 1 - (p : ℝ)) else 1 := by
    by_cases hj : j ∈ S
    · simpa only [if_pos hj] using bernoulliCoordinateLaw_singleton_real p hp (b j)
    · simp only [if_neg hj, measure_univ, ENNReal.toReal_one]
  simp_rw [hFactor]
  exact Fintype.prod_ite_mem S _

theorem bernoulli_row_zero_probability {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) :
    (bernoulliCubeLaw ι p hp).real {x | ∀ j ∈ S, x j = false} =
      (1 - (p : ℝ)) ^ S.card := by
  simpa only [BernoulliRowPattern, Bool.false_eq_true, if_false, Finset.prod_const] using
    bernoulli_row_pattern_probability p hp S (fun _ => false)

theorem bernoulli_row_single_probability {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) {j : ι} (hj : j ∈ S) :
    (bernoulliCubeLaw ι p hp).real {x | BernoulliRowSingle S j x} =
      (p : ℝ) * (1 - (p : ℝ)) ^ (S.card - 1) := by
  have hEvent : {x : ι → Bool | BernoulliRowSingle S j x} =
      {x | BernoulliRowPattern S (fun k => decide (k = j)) x} := by
    ext x
    simp only [Set.mem_setOf_eq, BernoulliRowSingle, BernoulliRowPattern]
    constructor
    · rintro ⟨hTrue, hFalse⟩ k hk
      by_cases hkj : k = j
      · simpa only [hkj, decide_true] using hTrue
      · simpa only [hkj, decide_false] using hFalse k hk hkj
    · intro hx
      refine ⟨by simpa only [decide_true] using hx j hj, ?_⟩
      intro k hk hkj
      simpa only [hkj, decide_false] using hx k hk
  rw [hEvent, bernoulli_row_pattern_probability,
    ← Finset.mul_prod_erase S (fun k => if decide (k = j) = true then (p : ℝ) else 1 - (p : ℝ)) hj]
  simp only [decide_true, ite_true]
  congr 1
  calc
    _ = ∏ _k ∈ S.erase j, (1 - (p : ℝ)) := by
      apply Finset.prod_congr rfl
      intro k hk
      simp only [(Finset.mem_erase.mp hk).1, decide_false, Bool.false_eq_true, if_false]
    _ = _ := by rw [Finset.prod_const, Finset.card_erase_of_mem hj]

theorem bernoulli_row_exactly_one_probability {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (S : Finset ι) :
    (bernoulliCubeLaw ι p hp).real {x | ∃ j ∈ S, BernoulliRowSingle S j x} =
      (S.card : ℝ) * p * (1 - (p : ℝ)) ^ (S.card - 1) := by
  let E := fun j : ι => {x : ι → Bool | BernoulliRowSingle S j x}
  have hEvent : {x : ι → Bool | ∃ j ∈ S, BernoulliRowSingle S j x} = ⋃ j ∈ S, E j := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E, exists_prop]
  have hDisjoint : Set.PairwiseDisjoint (S : Set ι) E := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hTrue : x j = true := hxj.1
    have hFalse : x j = false := hxi.2 j hj (Ne.symm hij)
    rw [hFalse] at hTrue
    exact Bool.false_ne_true hTrue
  rw [hEvent, measureReal_biUnion_finset hDisjoint
    (fun j _ => (Set.to_countable (E j)).measurableSet) (fun _ _ => measure_ne_top _ _)]
  calc
    _ = ∑ _j ∈ S, (p : ℝ) * (1 - (p : ℝ)) ^ (S.card - 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact bernoulli_row_single_probability p hp S hj
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end CircularLaw
