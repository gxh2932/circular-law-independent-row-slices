import CircularLaw.BernoulliWalkPatterns

/-!
# Exact covariance weights for centered Bernoulli entry words

Disjoint entry supports make the joint moment equal the product of the
individual moments. A singleton in the joint word makes both terms zero.
For a surviving joint word, the covariance weight is at most twice p to
the number of distinct entries. The product term uses the union of both
supports, retaining shared entries rather than counting them twice.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_centered_moment_abs_le_one (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    |bernoulliCenteredMoment p hp k| ≤ 1 := by
  cases k with
  | zero => simp [bernoulli_centered_moment_zero]
  | succ k =>
    cases k with
    | zero => simp [bernoulli_centered_moment_one]
    | succ k =>
      exact (bernoulli_centered_moment_abs_le_parameter p hp (by omega)).trans
        (by exact_mod_cast hp)

theorem bernoulli_word_weight_singleton_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (w : List ι) (e : ι) (he : w.count e = 1) :
    bernoulliWordMomentWeight p hp w = 0 := by
  rw [bernoulli_word_weight_eq_integral]
  exact bernoulli_centered_entry_word_singleton_zero p hp w e he

theorem bernoulli_word_weight_product_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (u v : List ι) :
    bernoulliWordMomentWeight p hp u * bernoulliWordMomentWeight p hp v =
      ∏ e ∈ (u ++ v).toFinset,
        bernoulliCenteredMoment p hp (u.count e) * bernoulliCenteredMoment p hp (v.count e) := by
  rw [bernoulli_word_weight_eq_full_product, bernoulli_word_weight_eq_full_product,
    ← Finset.prod_mul_distrib]
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro e _ he
  have hNot : e ∉ u ∧ e ∉ v := by simpa only [List.mem_toFinset, List.mem_append, not_or] using he
  rw [List.count_eq_zero_of_not_mem hNot.1, List.count_eq_zero_of_not_mem hNot.2,
    bernoulli_centered_moment_zero, one_mul]

theorem bernoulli_word_weight_disjoint_append {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (u v : List ι) (hDisjoint : Disjoint u.toFinset v.toFinset) :
    bernoulliWordMomentWeight p hp (u ++ v) =
      bernoulliWordMomentWeight p hp u * bernoulliWordMomentWeight p hp v := by
  rw [bernoulli_word_weight_product_support]
  unfold bernoulliWordMomentWeight
  apply Finset.prod_congr rfl
  intro e _
  by_cases hu : e ∈ u
  · have hv : e ∉ v := fun hv =>
      Finset.disjoint_left.mp hDisjoint (List.mem_toFinset.mpr hu) (List.mem_toFinset.mpr hv)
    rw [List.count_append, List.count_eq_zero_of_not_mem hv, Nat.add_zero,
      bernoulli_centered_moment_zero, mul_one]
  · rw [List.count_append, List.count_eq_zero_of_not_mem hu, Nat.zero_add,
      bernoulli_centered_moment_zero, one_mul]

def bernoulliWordCovarianceWeight {ι : Type*} [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (u v : List ι) : ℝ :=
  bernoulliWordMomentWeight p hp (u ++ v) -
    bernoulliWordMomentWeight p hp u * bernoulliWordMomentWeight p hp v

theorem bernoulli_word_covariance_weight_map {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ℝ≥0) (hp : p ≤ 1) (u v : List ι) (f : ι → κ) (hf : Function.Injective f) :
    bernoulliWordCovarianceWeight p hp (u.map f) (v.map f) =
      bernoulliWordCovarianceWeight p hp u v := by
  simp only [bernoulliWordCovarianceWeight, ← List.map_append, bernoulli_word_weight_map p hp _ f hf]

theorem bernoulli_word_covariance_weight_disjoint_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p : ℝ≥0) (hp : p ≤ 1) (u v : List ι)
    (hDisjoint : Disjoint u.toFinset v.toFinset) : bernoulliWordCovarianceWeight p hp u v = 0 := by
  rw [bernoulliWordCovarianceWeight, bernoulli_word_weight_disjoint_append p hp u v hDisjoint,
    sub_self]

theorem bernoulli_word_covariance_weight_singleton_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p : ℝ≥0) (hp : p ≤ 1) (u v : List ι) (e : ι)
    (he : (u ++ v).count e = 1) : bernoulliWordCovarianceWeight p hp u v = 0 := by
  have hCounts : u.count e + v.count e = 1 := by simpa only [List.count_append] using he
  have hEither : u.count e = 1 ∨ v.count e = 1 := by omega
  rw [bernoulliWordCovarianceWeight, bernoulli_word_weight_singleton_zero p hp _ e he]
  rcases hEither with hu | hv
  · rw [bernoulli_word_weight_singleton_zero p hp u e hu, zero_mul, sub_zero]
  · rw [bernoulli_word_weight_singleton_zero p hp v e hv, mul_zero, sub_zero]

theorem bernoulli_word_weight_product_abs_union_bound {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p : ℝ≥0) (hp : p ≤ 1) (u v : List ι) :
    |bernoulliWordMomentWeight p hp u * bernoulliWordMomentWeight p hp v| ≤
      (p : ℝ) ^ (u ++ v).toFinset.card := by
  by_cases hu : ∀ e, u.count e ≠ 1
  · by_cases hv : ∀ e, v.count e ≠ 1
    · rw [bernoulli_word_weight_product_support, Finset.abs_prod]
      calc
        _ ≤ ∏ _e ∈ (u ++ v).toFinset, (p : ℝ) := by
          apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          intro e he
          rw [abs_mul]
          have hMem : e ∈ u ∨ e ∈ v := by simpa only [List.mem_toFinset, List.mem_append] using he
          rcases hMem with heU | heV
          · have hPos := List.count_pos_iff.mpr heU
            have hMu := bernoulli_centered_moment_abs_le_parameter p hp
              (k := u.count e) (by have h := hu e; omega)
            exact (mul_le_mul_of_nonneg_right hMu (abs_nonneg _)).trans
              (mul_le_of_le_one_right p.coe_nonneg (bernoulli_centered_moment_abs_le_one p hp _))
          · have hPos := List.count_pos_iff.mpr heV
            have hMv := bernoulli_centered_moment_abs_le_parameter p hp
              (k := v.count e) (by have h := hv e; omega)
            exact (mul_le_mul_of_nonneg_left hMv (abs_nonneg _)).trans
              (mul_le_of_le_one_left p.coe_nonneg (bernoulli_centered_moment_abs_le_one p hp _))
        _ = _ := by simp
    · push_neg at hv
      obtain ⟨e, he⟩ := hv
      rw [bernoulli_word_weight_singleton_zero p hp v e he, mul_zero, abs_zero]
      positivity
  · push_neg at hu
    obtain ⟨e, he⟩ := hu
    rw [bernoulli_word_weight_singleton_zero p hp u e he, zero_mul, abs_zero]
    positivity

theorem bernoulli_word_covariance_weight_abs_bound {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p : ℝ≥0) (hp : p ≤ 1) (u v : List ι)
    (hNoSingleton : ∀ e, (u ++ v).count e ≠ 1) :
    |bernoulliWordCovarianceWeight p hp u v| ≤ 2 * (p : ℝ) ^ (u ++ v).toFinset.card := by
  have hJoint : |bernoulliWordMomentWeight p hp (u ++ v)| ≤
      (p : ℝ) ^ (u ++ v).toFinset.card := by
    rw [bernoulli_word_weight_eq_integral]
    exact bernoulli_centered_entry_word_integral_abs_bound p hp _ hNoSingleton
  have hProduct := bernoulli_word_weight_product_abs_union_bound p hp u v
  have hTriangle : |bernoulliWordCovarianceWeight p hp u v| ≤
      |bernoulliWordMomentWeight p hp (u ++ v)| +
        |bernoulliWordMomentWeight p hp u * bernoulliWordMomentWeight p hp v| := by
    simpa only [bernoulliWordCovarianceWeight, sub_zero, zero_sub, abs_neg] using
      abs_sub_le (bernoulliWordMomentWeight p hp (u ++ v)) 0
        (bernoulliWordMomentWeight p hp u * bernoulliWordMomentWeight p hp v)
  exact hTriangle.trans (by linarith)

end CircularLaw
