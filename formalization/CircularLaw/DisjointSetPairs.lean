import CircularLaw.RowWitnessBounds

/-!
# Counting disjoint pairs of coordinate sets

A pair is determined by its union and its left subset. The resulting
count is `choose(n,t) * choose(t,s)`, including empty or impossible sizes.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

abbrev DisjointSetPair (n s t : ℕ) :=
  {p : Finset (Fin n) × Finset (Fin n) //
    Disjoint p.1 p.2 ∧ p.1.card = s ∧ (p.1 ∪ p.2).card = t}

abbrev UnionAndLeftSubset (n s t : ℕ) :=
  Σ U : {U : Finset (Fin n) // U.card = t},
    {L : Finset (Fin n) // L ⊆ U.val ∧ L.card = s}

def disjointSetPairEquiv (n s t : ℕ) :
    DisjointSetPair n s t ≃ UnionAndLeftSubset n s t where
  toFun p := ⟨⟨p.val.1 ∪ p.val.2, p.property.2.2⟩,
    ⟨p.val.1, Finset.subset_union_left, p.property.2.1⟩⟩
  invFun x := ⟨(x.2.val, x.1.val \ x.2.val), Finset.disjoint_sdiff,
    x.2.property.2, by rw [Finset.union_sdiff_of_subset x.2.property.1]; exact x.1.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Finset.union_sdiff_cancel_left p.property.1
  right_inv x := by
    rcases x with ⟨U, L⟩
    rcases U with ⟨U, hU⟩
    rcases L with ⟨L, hL⟩
    dsimp only
    have hUnion := Finset.union_sdiff_of_subset hL.1
    apply Sigma.ext (Subtype.ext hUnion)
    exact (Subtype.heq_iff_coe_eq (fun A => by
      change (A ⊆ L ∪ U \ L ∧ A.card = s) ↔ (A ⊆ U ∧ A.card = s)
      rw [hUnion])).mpr rfl

theorem card_fixed_size_subsets (n t : ℕ) :
    Fintype.card {U : Finset (Fin n) // U.card = t} = n.choose t := by
  let e : {U : Finset (Fin n) // U.card = t} ≃
      {U : Finset (Fin n) // U ∈ Finset.univ.powersetCard t} :=
    Equiv.subtypeEquivRight (fun U => by
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and])
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]

theorem card_fixed_size_subsets_of_set {n : ℕ} (U : Finset (Fin n)) (s : ℕ) :
    Fintype.card {L : Finset (Fin n) // L ⊆ U ∧ L.card = s} = U.card.choose s := by
  let e : {L : Finset (Fin n) // L ⊆ U ∧ L.card = s} ≃
      {L : Finset (Fin n) // L ∈ U.powersetCard s} :=
    Equiv.subtypeEquivRight (fun _ => Finset.mem_powersetCard.symm)
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powersetCard]

theorem card_disjoint_set_pairs (n s t : ℕ) :
    Fintype.card (DisjointSetPair n s t) = n.choose t * t.choose s := by
  rw [Fintype.card_congr (disjointSetPairEquiv n s t)]
  change Fintype.card (Σ U : {U : Finset (Fin n) // U.card = t},
    {L : Finset (Fin n) // L ⊆ U.val ∧ L.card = s}) = _
  rw [Fintype.card_sigma]
  simp_rw [card_fixed_size_subsets_of_set]
  have hSum : (∑ U : {U : Finset (Fin n) // U.card = t}, U.val.card.choose s) =
      ∑ _U : {U : Finset (Fin n) // U.card = t}, t.choose s := by
    apply Finset.sum_congr rfl
    intro U _
    rw [U.property]
  rw [hSum]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_fixed_size_subsets]
  simp only [Nat.cast_id]

end CircularLaw
