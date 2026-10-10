import CircularLaw.EqualBlock
import CircularLaw.Covariance

/-!
# Exact singleton witness probabilities on a row slice

Fixing the unique selected coordinate in a set `J` leaves an arbitrary
`d-1` subset of its complement. Deletion and insertion give the exact
binomial count, with no coordinate independence assumption.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem card_slice_inter_singleton {n d : ℕ} (hd : 0 < d)
    (J : Finset (Fin n)) (j : Fin n) (hj : j ∈ J) :
    Nat.card {S : RowSlice n d // S.val ∩ J = {j}} =
      (n - J.card).choose (d - 1) := by
  let A := (Finset.univ.powersetCard d).filter (fun S => S ∩ J = {j})
  let B := (Finset.univ \ J).powersetCard (d - 1)
  have hCard : A.card = B.card := by
    refine Finset.card_bij' (fun S _ => S.erase j) (fun T _ => insert j T) ?_ ?_ ?_ ?_
    · intro S hS
      obtain ⟨hSd, hInter⟩ := Finset.mem_filter.mp hS
      have hSize := (Finset.mem_powersetCard.mp hSd).2
      have hjS : j ∈ S := by
        have hMem : j ∈ S ∩ J := by rw [hInter]; simp
        exact (Finset.mem_inter.mp hMem).1
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro k hk
        obtain ⟨hkj, hkS⟩ := Finset.mem_erase.mp hk
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hkJ
        have hMem : k ∈ S ∩ J := Finset.mem_inter.mpr ⟨hkS, hkJ⟩
        rw [hInter] at hMem
        exact hkj (Finset.mem_singleton.mp hMem)
      · rw [Finset.card_erase_of_mem hjS, hSize]
    · intro T hT
      obtain ⟨hSub, hSize⟩ := Finset.mem_powersetCard.mp hT
      have hjT : j ∉ T := fun h => (Finset.mem_sdiff.mp (hSub h)).2 hj
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        refine ⟨Finset.subset_univ _, ?_⟩
        rw [Finset.card_insert_of_notMem hjT, hSize]
        omega
      · ext k
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hk
          rcases hk.1 with hEq | hkT
          · exact hEq
          · exact False.elim ((Finset.mem_sdiff.mp (hSub hkT)).2 hk.2)
        · intro hEq
          subst k
          exact ⟨Or.inl rfl, hj⟩
    · intro S hS
      have hInter := (Finset.mem_filter.mp hS).2
      have hjS : j ∈ S := by
        have hMem : j ∈ S ∩ J := by rw [hInter]; simp
        exact (Finset.mem_inter.mp hMem).1
      exact Finset.insert_erase hjS
    · intro T hT
      have hjT : j ∉ T := fun h =>
        (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hT).1 h)).2 hj
      exact Finset.erase_insert hjT
  let e : {S : RowSlice n d // S.val ∩ J = {j}} ≃ {S : Finset (Fin n) // S ∈ A} :=
    { toFun := fun S => ⟨S.val.val, Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.val.property⟩, S.property⟩⟩
      invFun := fun S => ⟨⟨S.val, (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp S.property).1).2⟩, (Finset.mem_filter.mp S.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, hCard]
  simp only [B, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ J),
    Finset.card_univ, Fintype.card_fin]

theorem slice_inter_singleton_probability {n d : ℕ} (hd : 0 < d)
    (J : Finset (Fin n)) (j : Fin n) (hj : j ∈ J) :
    uniformProbability (fun S : RowSlice n d => S.val ∩ J = {j}) =
      ((n - J.card).choose (d - 1) : ℝ) / n.choose d := by
  rw [uniformProbability, card_slice_inter_singleton hd J j hj,
    Nat.card_eq_fintype_card, card_rowSlice]

end CircularLaw
