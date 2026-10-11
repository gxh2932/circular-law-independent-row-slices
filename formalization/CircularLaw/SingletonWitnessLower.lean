import CircularLaw.RowWitnessProbability

/-!
# Singleton witness lower bounds from the exact coordinate laws

If a selected coordinate is not the unique coordinate in `J`, another
coordinate of `J` is selected. Taking expectations of this deterministic
alternative gives a lower bound using the checked pair probabilities.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem singleton_witness_indicator_bound {n d : ℕ} (J : Finset (Fin n))
    (j : Fin n) (hj : j ∈ J) (S : RowSlice n d) :
    (if j ∈ S.val then (1 : ℝ) else 0) ≤
      (if S.val ∩ J = {j} then (1 : ℝ) else 0) +
        ∑ k ∈ J.erase j, if j ∈ S.val ∧ k ∈ S.val then (1 : ℝ) else 0 := by
  by_cases hjS : j ∈ S.val
  · rw [if_pos hjS]
    by_cases hInter : S.val ∩ J = {j}
    · rw [if_pos hInter]
      have hSum : (0 : ℝ) ≤ ∑ k ∈ J.erase j,
          if j ∈ S.val ∧ k ∈ S.val then (1 : ℝ) else 0 :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      linarith
    · rw [if_neg hInter, zero_add]
      have hOther : ∃ k ∈ J.erase j, k ∈ S.val := by
        by_contra h
        apply hInter
        ext k
        simp only [Finset.mem_inter, Finset.mem_singleton]
        constructor
        · intro hk
          by_contra hkj
          exact h ⟨k, Finset.mem_erase.mpr ⟨hkj, hk.2⟩, hk.1⟩
        · intro hEq
          subst k
          exact ⟨hjS, hj⟩
      obtain ⟨k, hkJ, hkS⟩ := hOther
      have h := Finset.single_le_sum
        (f := fun k => if j ∈ S.val ∧ k ∈ S.val then (1 : ℝ) else 0)
        (fun _ _ => by positivity) hkJ
      have hBoth : j ∈ S.val ∧ k ∈ S.val := ⟨hjS, hkS⟩
      simpa only [if_pos hBoth] using h
  · rw [if_neg hjS]
    positivity

theorem slice_inter_singleton_probability_lower {n d : ℕ} (hn : 2 ≤ n)
    (hd : 0 < d) (hdn : d ≤ n) (J : Finset (Fin n)) (j : Fin n) (hj : j ∈ J) :
    (d : ℝ) / n * (1 - ((d : ℝ) - 1) * ((J.card : ℝ) - 1) / ((n : ℝ) - 1)) ≤
      uniformProbability (fun S : RowSlice n d => S.val ∩ J = {j}) := by
  have h := finiteMean_mono (singleton_witness_indicator_bound J j hj (d := d))
  rw [finiteMean_indicator, row_coordinate_probability hd hdn j, finiteMean_add,
    finiteMean_indicator, finiteMean_finset_sum] at h
  simp only [finiteMean_indicator] at h
  have hPairs : (∑ k ∈ J.erase j, uniformProbability
      (fun S : RowSlice n d => j ∈ S.val ∧ k ∈ S.val)) =
        ((J.card : ℝ) - 1) * ((d : ℝ) * (d - 1) / ((n : ℝ) * (n - 1))) := by
    calc
      _ = ∑ _k ∈ J.erase j, (d : ℝ) * (d - 1) / ((n : ℝ) * (n - 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact row_pair_probability hdn j k (Finset.mem_erase.mp hk).1.symm
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hj,
          Nat.cast_sub (Finset.card_pos.mpr ⟨j, hj⟩)]
        simp only [Nat.cast_one]
  rw [hPairs] at h
  have hnReal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnPred : (0 : ℝ) < (n : ℝ) - 1 := by
    have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hExpand : (d : ℝ) / n * (1 - ((d : ℝ) - 1) * ((J.card : ℝ) - 1) / ((n : ℝ) - 1)) =
      (d : ℝ) / n - ((J.card : ℝ) - 1) * ((d : ℝ) * (d - 1) / ((n : ℝ) * (n - 1))) := by
    field_simp
  rw [hExpand]
  linarith

theorem unique_row_witness_probability_lower {n d : ℕ} (hn : 2 ≤ n)
    (hd : 0 < d) (hdn : d ≤ n) (L J : Finset (Fin n)) (hLJ : L ⊆ J) :
    (d : ℝ) * L.card / n *
      (1 - ((d : ℝ) - 1) * ((J.card : ℝ) - 1) / ((n : ℝ) - 1)) ≤
        uniformProbability (uniqueRowWitness (d := d) L J) := by
  change _ ≤ uniformProbability (fun S : RowSlice n d => ∃ j ∈ L, S.val ∩ J = {j})
  rw [uniformProbability_finset_exists_eq L
    (fun j (S : RowSlice n d) => S.val ∩ J = {j})]
  · have h := Finset.sum_le_sum (fun j (hj : j ∈ L) =>
      slice_inter_singleton_probability_lower hn hd hdn J j (hLJ hj))
    rw [Finset.sum_const, nsmul_eq_mul] at h
    convert h using 1
    ring
  · intro S i _ j _ hi hj
    exact Finset.singleton_injective (hi.symm.trans hj)

end CircularLaw
