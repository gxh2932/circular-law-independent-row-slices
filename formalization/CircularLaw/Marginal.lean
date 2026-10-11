import CircularLaw.FiniteProbability

/-!
# Coordinate marginals of an exact row slice

Coordinates of a slice are dependent, but each individual coordinate has
probability `d/n` of being one. The proof counts supports containing the
coordinate by deletion, rather than assuming Bernoulli independence.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

theorem card_slices_containing {n d : ℕ} (hd : 0 < d) (j : Fin n) :
    (((Finset.univ : Finset (Fin n)).powersetCard d).filter
      fun S => j ∈ S).card = (n - 1).choose (d - 1) := by
  classical
  have hcard : (((Finset.univ : Finset (Fin n)).powersetCard d).filter
      fun S => j ∈ S).card = ((Finset.univ.erase j).powersetCard (d - 1)).card := by
    refine Finset.card_bij' (fun S _ => S.erase j) (fun T _ => insert j T) ?_ ?_ ?_ ?_
    · intro S hS
      rcases Finset.mem_filter.mp hS with ⟨hS, hjS⟩
      rcases Finset.mem_powersetCard.mp hS with ⟨_, hsize⟩
      apply Finset.mem_powersetCard.mpr
      exact ⟨Finset.erase_subset_erase j (Finset.subset_univ _), by
        rw [Finset.card_erase_of_mem hjS, hsize]⟩
    · intro T hT
      rcases Finset.mem_powersetCard.mp hT with ⟨hsub, hsize⟩
      have hjT : j ∉ T := fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩,
        Finset.mem_insert_self _ _⟩
      rw [Finset.card_insert_of_notMem hjT, hsize]
      omega
    · intro S hS
      exact Finset.insert_erase (Finset.mem_filter.mp hS).2
    · intro T hT
      have hjT : j ∉ T := fun h =>
        (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hT).1 h)).1 rfl
      exact Finset.erase_insert hjT
  simpa [Finset.card_powersetCard] using hcard

/-- A coordinate of the uniform exact slice has the Bernoulli marginal `d/n`. -/
theorem row_coordinate_probability {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) (j : Fin n) :
    uniformProbability (fun s : RowSlice n d => j ∈ s.val) = (d : ℝ) / n := by
  classical
  let family := ((Finset.univ : Finset (Fin n)).powersetCard d).filter fun S => j ∈ S
  let e : {s : RowSlice n d // j ∈ s.val} ≃ {S : Finset (Fin n) // S ∈ family} :=
    { toFun := fun s => ⟨s.val.val, Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, s.val.property⟩, s.property⟩⟩
      invFun := fun S => ⟨⟨S.val,
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp S.property).1).2⟩,
        (Finset.mem_filter.mp S.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfamily : Nat.card {s : RowSlice n d // j ∈ s.val} = (n - 1).choose (d - 1) := by
    rw [Nat.card_congr e]
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact card_slices_containing hd j
  have htotal : Nat.card (RowSlice n d) = n.choose d := by
    rw [Nat.card_eq_fintype_card, card_rowSlice]
  have hn : 0 < n := lt_of_lt_of_le hd hdn
  have hpredn : n - 1 + 1 = n := by omega
  have hpredd : d - 1 + 1 = d := by omega
  have hchoose := Nat.add_one_mul_choose_eq (n - 1) (d - 1)
  rw [hpredn, hpredd] at hchoose
  have hchoose' : (n : ℝ) * (n - 1).choose (d - 1) = (n.choose d : ℝ) * d := by
    exact_mod_cast hchoose
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have ht' : (n.choose d : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hdn).ne'
  rw [uniformProbability, hfamily, htotal]
  apply (div_eq_div_iff ht' hn').mpr
  nlinarith [hchoose']

end CircularLaw
