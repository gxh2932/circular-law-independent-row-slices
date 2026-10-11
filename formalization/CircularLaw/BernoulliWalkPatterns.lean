import CircularLaw.FiniteKernelPartition
import CircularLaw.BernoulliNormalizedWordMeans
import CircularLaw.BernoulliWalkVertexBounds

/-!
# Actual Bernoulli trace sums indexed by finite equality patterns

The marginal moment product is unchanged under injective relabeling of
entries. For each vertex kernel, evaluate it on the canonical quotient
walk. Grouping the actual matrix trace formula by that kernel then gives
a finite sum over patterns, whose coefficients are exact falling factorials.
The pattern set depends only on the fixed word length, not on the matrix
dimension. No Bernoulli moment limit or weak convergence is assumed.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix NNReal

namespace CircularLaw

local instance bernoulliWalkPatternBEq (n : ℕ) : BEq (Fin n × Fin n) := instBEqOfDecidableEq

local instance bernoulliQuotientPatternBEq {α : Type*} (s : Setoid α) :
    BEq (Quotient s × Quotient s) := instBEqOfDecidableEq

def bernoulliWordMomentWeight {ι : Type*} [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : List ι) : ℝ :=
  ∏ e ∈ w.toFinset, bernoulliCenteredMoment p hp (w.count e)

theorem bernoulli_word_weight_eq_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : List ι) :
    bernoulliWordMomentWeight p hp w =
      ∫ x : ι → Bool, bernoulliCenteredEntryWord p w x ∂bernoulliCubeLaw ι p hp :=
  (bernoulli_centered_entry_word_integral_support p hp w).symm

theorem bernoulli_word_weight_eq_full_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : List ι) :
    bernoulliWordMomentWeight p hp w = ∏ e, bernoulliCenteredMoment p hp (w.count e) := by
  rw [bernoulli_word_weight_eq_integral, bernoulli_centered_entry_word_integral]

theorem bernoulli_word_weight_map {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ℝ≥0) (hp : p ≤ 1) (w : List ι) (f : ι → κ) (hf : Function.Injective f) :
    bernoulliWordMomentWeight p hp (w.map f) = bernoulliWordMomentWeight p hp w := by
  have hSet : (w.map f).toFinset = w.toFinset.image f := by
    ext e
    simp
  unfold bernoulliWordMomentWeight
  rw [hSet, Finset.prod_image hf.injOn]
  simp only [List.count_map_of_injective w f hf]

def bernoulliPatternEntryWord {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) : List (Quotient s × Quotient s) :=
  List.ofFn (orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s))

def bernoulliWalkPatternWeight {k : ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1))) : ℝ :=
  bernoulliWordMomentWeight p hp (bernoulliPatternEntryWord b s)

theorem bernoulli_pattern_entry_word_length {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) : (bernoulliPatternEntryWord b s).length = k + 1 := by
  simp only [bernoulliPatternEntryWord, List.length_ofFn]

theorem bernoulli_walk_entries_kernel_map {n k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (v : Fin (k + 1) → Fin n)
    (hKernel : ∀ a c, v a = v c ↔ s a c) :
    bernoulliWalkEntries b v = (bernoulliPatternEntryWord b s).map
      (Prod.map ((fixedKernelColoringsEquiv s ⟨v, hKernel⟩) : Quotient s → Fin n)
        ((fixedKernelColoringsEquiv s ⟨v, hKernel⟩) : Quotient s → Fin n)) := by
  rw [bernoulliWalkEntries, bernoulliPatternEntryWord, List.map_ofFn]
  apply congrArg List.ofFn
  funext a
  cases h : b a <;> simp [orientedClosedWalkEntry, h, fixedKernelColoringsEquiv]

theorem bernoulli_walk_weight_constant_on_kernel {n k : ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1)))
    (v : Fin (k + 1) → Fin n) (hKernel : ∀ a c, v a = v c ↔ s a c) :
    bernoulliWordMomentWeight p hp (bernoulliWalkEntries b v) =
      bernoulliWalkPatternWeight p hp b s := by
  rw [bernoulli_walk_entries_kernel_map b s v hKernel]
  unfold bernoulliWalkPatternWeight
  apply bernoulli_word_weight_map
  intro x y h
  apply Prod.ext
  · exact (fixedKernelColoringsEquiv s ⟨v, hKernel⟩).injective (congrArg Prod.fst h)
  · exact (fixedKernelColoringsEquiv s ⟨v, hKernel⟩).injective (congrArg Prod.snd h)

theorem bernoulli_matrix_word_pattern_integral (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (k : ℕ) (b : Fin (k + 1) → Bool) :
    (∫ x, (matrixAdjointWord (bernoulliCenteredSquareMatrix p x) (List.ofFn b)).trace.re
      ∂bernoulliSquareMatrixLaw n p hp) =
      ∑ s : Setoid (Fin (k + 1)),
        (n.descFactorial (Nat.card (Quotient s)) : ℝ) * bernoulliWalkPatternWeight p hp b s := by
  rw [bernoulli_centered_matrix_word_trace_integral]
  simp_rw [← bernoulli_word_weight_eq_full_product]
  exact sum_kernel_constant_fin_colorings n _ _
    (fun s v h => bernoulli_walk_weight_constant_on_kernel p hp b s v h)

theorem bernoulli_normalized_word_pattern_formula {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (k : ℕ) (b : Fin (k + 1) → Bool) :
    bernoulliNormalizedWordMean n d (List.ofFn b) =
      ((Real.sqrt (d : ℝ))⁻¹ ^ (k + 1) / (n : ℝ)) *
        ∑ s : Setoid (Fin (k + 1)),
          (n.descFactorial (Nat.card (Quotient s)) : ℝ) *
            bernoulliWalkPatternWeight (rowBernoulliParameter n d)
              (rowBernoulliParameter_le_one hn hdn) b s := by
  rw [bernoulli_normalized_word_mean_formula hn hdn k b]
  congr 1
  rw [← bernoulli_centered_matrix_word_trace_integral, bernoulli_matrix_word_pattern_integral]

theorem bernoulli_pattern_weight_singleton_zero {k : ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1))) (e : Quotient s × Quotient s)
    (hCount : (bernoulliPatternEntryWord b s).count e = 1) :
    bernoulliWalkPatternWeight p hp b s = 0 := by
  rw [bernoulliWalkPatternWeight, bernoulli_word_weight_eq_integral]
  exact bernoulli_centered_entry_word_singleton_zero p hp _ e hCount

theorem bernoulli_pattern_weight_abs_bound {k : ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1)))
    (hNoSingleton : ∀ e, (bernoulliPatternEntryWord b s).count e ≠ 1) :
    |bernoulliWalkPatternWeight p hp b s| ≤
      (p : ℝ) ^ (bernoulliPatternEntryWord b s).toFinset.card := by
  rw [bernoulliWalkPatternWeight, bernoulli_word_weight_eq_integral]
  exact bernoulli_centered_entry_word_integral_abs_bound p hp _ hNoSingleton

theorem bernoulli_paired_pattern_weight {k : ℕ} (p : ℝ≥0) (hp : p ≤ 1)
    (b : Fin (k + 1) → Bool) (s : Setoid (Fin (k + 1)))
    (hPaired : ∀ e ∈ (bernoulliPatternEntryWord b s).toFinset,
      (bernoulliPatternEntryWord b s).count e = 2) :
    bernoulliWalkPatternWeight p hp b s =
      ((p : ℝ) * (1 - (p : ℝ))) ^ (bernoulliPatternEntryWord b s).toFinset.card := by
  rw [bernoulliWalkPatternWeight, bernoulli_word_weight_eq_integral]
  exact bernoulli_centered_entry_paired_word_integral p hp _ hPaired

def bernoulliPatternVertexCount {k : ℕ} (s : Setoid (Fin (k + 1))) : ℕ :=
  Nat.card (Quotient s)

def bernoulliPatternEntryCount {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) : ℕ := (bernoulliPatternEntryWord b s).toFinset.card

theorem bernoulli_pattern_quotient_range_card {k : ℕ} (s : Setoid (Fin (k + 1))) :
    Nat.card (Set.range (Quotient.mk s)) = bernoulliPatternVertexCount s := by
  have hRange : Set.range (Quotient.mk s) = Set.univ :=
    Set.range_eq_univ.mpr Quotient.mk_surjective
  simp only [hRange, Nat.card_eq_fintype_card, Fintype.card_setUniv,
    bernoulliPatternVertexCount]

theorem bernoulli_pattern_entry_range_card {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) :
    Nat.card (Set.range (orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s))) =
      bernoulliPatternEntryCount b s := by
  let e : Set.range (orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s)) ≃
      (bernoulliPatternEntryWord b s).toFinset :=
    Equiv.subtypeEquivRight (fun _ => by
      simp only [List.mem_toFinset, bernoulliPatternEntryWord, List.mem_ofFn'])
  exact (Nat.card_congr e).trans (by
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe, bernoulliPatternEntryCount])

theorem bernoulli_pattern_vertex_bound {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) :
    bernoulliPatternVertexCount s ≤ bernoulliPatternEntryCount b s + 1 := by
  have h := closed_walk_visited_vertex_bound (finRotate (k + 1)) b (Quotient.mk s)
    (fin_rotate_same_cycle k)
  rw [bernoulli_pattern_quotient_range_card, bernoulli_pattern_entry_range_card] at h
  exact h

theorem bernoulli_pattern_surviving_entry_bound {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1)))
    (hNoSingleton : ∀ e, (bernoulliPatternEntryWord b s).count e ≠ 1) :
    2 * bernoulliPatternEntryCount b s ≤ k + 1 := by
  simpa only [bernoulliPatternEntryCount, bernoulli_pattern_entry_word_length] using
    bernoulli_centered_entry_word_distinct_count_bound (bernoulliPatternEntryWord b s) hNoSingleton

theorem entry_word_paired_of_maximal_count {ι : Type*} [DecidableEq ι] (w : List ι)
    (hNoSingleton : ∀ e, w.count e ≠ 1) (hMax : 2 * w.toFinset.card = w.length) :
    ∀ e ∈ w.toFinset, w.count e = 2 := by
  have hLower (e : ι) (he : e ∈ w.toFinset) : 2 ≤ w.count e := by
    have hPos := List.count_pos_iff.mpr (List.mem_toFinset.mp he)
    have h := hNoSingleton e
    omega
  intro e he
  by_contra hne
  have hStrict : 2 < w.count e := by have h := hLower e he; omega
  have hSum := Finset.sum_lt_sum hLower ⟨e, he, hStrict⟩
  rw [List.sum_toFinset_count_eq_length] at hSum
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at hSum
  omega

theorem bernoulli_maximal_entry_pattern_paired {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1)))
    (hNoSingleton : ∀ e, (bernoulliPatternEntryWord b s).count e ≠ 1)
    (hMax : 2 * bernoulliPatternEntryCount b s = k + 1) :
    ∀ e ∈ (bernoulliPatternEntryWord b s).toFinset,
      (bernoulliPatternEntryWord b s).count e = 2 := by
  apply entry_word_paired_of_maximal_count _ hNoSingleton
  simpa only [bernoulliPatternEntryCount, bernoulli_pattern_entry_word_length] using hMax

end CircularLaw
