import CircularLaw.FiniteDisjointEvents

/-!
# The unique-coordinate and equal-block row witness laws

Summing over the disjoint possible singleton coordinates gives the exact
probability `|L|*choose(n-|J|,d-1)/choose(n,d)`. For disjoint `L,R`, the
event is exactly one coordinate in `L` and none in `R`.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def uniqueRowWitness {n d : ℕ} (L J : Finset (Fin n)) (S : RowSlice n d) : Prop :=
  ∃ j ∈ L, S.val ∩ J = {j}

theorem unique_row_witness_probability {n d : ℕ} (hd : 0 < d)
    (L J : Finset (Fin n)) (hLJ : L ⊆ J) :
    uniformProbability (uniqueRowWitness (d := d) L J) =
      (L.card : ℝ) * ((n - J.card).choose (d - 1) : ℝ) / n.choose d := by
  change uniformProbability (fun S : RowSlice n d => ∃ j ∈ L, S.val ∩ J = {j}) = _
  rw [uniformProbability_finset_exists_eq L
    (fun j (S : RowSlice n d) => S.val ∩ J = {j})]
  · calc
      _ = ∑ _j ∈ L, ((n - J.card).choose (d - 1) : ℝ) / n.choose d := by
        apply Finset.sum_congr rfl
        intro j hj
        exact slice_inter_singleton_probability hd J j (hLJ hj)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  · intro S i _ j _ hi hj
    have hSingleton : ({i} : Finset (Fin n)) = {j} := hi.symm.trans hj
    exact Finset.singleton_injective hSingleton

theorem uniqueRowWitness_union_iff {n d : ℕ} (L R : Finset (Fin n))
    (hLR : Disjoint L R) (S : RowSlice n d) :
    uniqueRowWitness L (L ∪ R) S ↔ (S.val ∩ L).card = 1 ∧ Disjoint S.val R := by
  constructor
  · rintro ⟨j, hjL, hInter⟩
    have hjS : j ∈ S.val := by
      have hMem : j ∈ S.val ∩ (L ∪ R) := by rw [hInter]; simp
      exact (Finset.mem_inter.mp hMem).1
    have hLeft : S.val ∩ L = {j} := by
      ext k
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · intro hk
        have hMem : k ∈ S.val ∩ (L ∪ R) :=
          Finset.mem_inter.mpr ⟨hk.1, Finset.mem_union_left R hk.2⟩
        rw [hInter] at hMem
        exact Finset.mem_singleton.mp hMem
      · intro hEq
        subst k
        exact ⟨hjS, hjL⟩
    refine ⟨by rw [hLeft]; simp, Finset.disjoint_left.mpr ?_⟩
    intro k hkS hkR
    have hMem : k ∈ S.val ∩ (L ∪ R) :=
      Finset.mem_inter.mpr ⟨hkS, Finset.mem_union_right L hkR⟩
    rw [hInter] at hMem
    have hEq := Finset.mem_singleton.mp hMem
    subst k
    exact Finset.disjoint_left.mp hLR hjL hkR
  · rintro ⟨hCard, hDis⟩
    obtain ⟨j, hLeft⟩ := Finset.card_eq_one.mp hCard
    have hjL : j ∈ L := by
      have hMem : j ∈ S.val ∩ L := by rw [hLeft]; simp
      exact (Finset.mem_inter.mp hMem).2
    refine ⟨j, hjL, ?_⟩
    rw [Finset.inter_union_distrib_left, hLeft, Finset.disjoint_iff_inter_eq_empty.mp hDis, Finset.union_empty]

theorem unique_coordinate_witness_probability {n d : ℕ} (hd : 0 < d)
    (L R : Finset (Fin n)) (hLR : Disjoint L R) :
    uniformProbability (fun S : RowSlice n d => (S.val ∩ L).card = 1 ∧ Disjoint S.val R) =
      (L.card : ℝ) * ((n - (L ∪ R).card).choose (d - 1) : ℝ) / n.choose d := by
  have hEvent : (fun S : RowSlice n d => (S.val ∩ L).card = 1 ∧ Disjoint S.val R) =
      uniqueRowWitness L (L ∪ R) := by
    funext S
    exact propext (uniqueRowWitness_union_iff L R hLR S).symm
  rw [hEvent]
  exact unique_row_witness_probability hd L (L ∪ R) Finset.subset_union_left

theorem uniqueRowWitness_self_iff {n d : ℕ} (J : Finset (Fin n)) (S : RowSlice n d) :
    uniqueRowWitness J J S ↔ (S.val ∩ J).card = 1 := by
  constructor
  · rintro ⟨j, _, hInter⟩
    rw [hInter]
    simp
  · intro hCard
    obtain ⟨j, hInter⟩ := Finset.card_eq_one.mp hCard
    refine ⟨j, ?_, hInter⟩
    have hMem : j ∈ S.val ∩ J := by rw [hInter]; simp
    exact (Finset.mem_inter.mp hMem).2

theorem block_witness_probability {n d : ℕ} (hd : 0 < d) (J : Finset (Fin n)) :
    uniformProbability (fun S : RowSlice n d => (S.val ∩ J).card = 1) =
      (J.card : ℝ) * ((n - J.card).choose (d - 1) : ℝ) / n.choose d := by
  have hEvent : (fun S : RowSlice n d => (S.val ∩ J).card = 1) = uniqueRowWitness J J := by
    funext S
    exact propext (uniqueRowWitness_self_iff J S).symm
  rw [hEvent]
  exact unique_row_witness_probability hd J J (Finset.Subset.refl _)

end CircularLaw
