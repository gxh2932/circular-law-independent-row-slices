import CircularLaw.BernoulliLeadingPartners

/-!
# A Bernoulli leading kernel is exactly its Gaussian pairing kernel

Direct positions biject with the distinct ordered entries. The compatible
partner involution gives the Gaussian endpoint constraints. Their generated
quotient maps onto the original kernel quotient. The Gaussian vertex bound
and the Bernoulli maximal vertex count force this map to be a bijection,
so no additional vertex identifications remain.
-/

noncomputable section
open Classical

namespace CircularLaw

def gaussianWordPairingSetoid {α : Type*} (b : α → Bool) (ρ : Equiv.Perm α)
    (e : GaussianWordPairing b) : Setoid α :=
  Relation.EqvGen.setoid (pairedWalkRelation ρ
    (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val))

theorem gaussian_word_pairing_quotient_card {α : Type*} [Fintype α] [DecidableEq α]
    (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b) :
    Nat.card (Quotient (gaussianWordPairingSetoid b ρ e)) = gaussianWordVertexExponent b ρ e := by
  simp only [Nat.card_eq_fintype_card, gaussianWordPairingSetoid,
    gaussianWordVertexExponent, relationClassCount]

def bernoulliLeadingDirectEntry {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (a : GaussianDirectPositions b) :
    Set.range (orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s)) :=
  ⟨orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) a.val, ⟨a.val, rfl⟩⟩

theorem bernoulli_leading_direct_entry_bijective {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) :
    Function.Bijective (bernoulliLeadingDirectEntry b s) := by
  constructor
  · intro a c h
    have he := congrArg Subtype.val h
    rcases (bernoulli_leading_entry_fiber_iff b s hLeading c.val a.val).mp he with he | he
    · exact Subtype.ext he
    · have hb := (bernoulli_leading_partner_spec b s hLeading c.val).2
      rw [← he, a.property, c.property] at hb
      exact False.elim (hb rfl)
  · rintro ⟨e, a, rfl⟩
    cases ha : b a with
    | false => exact ⟨⟨a, ha⟩, rfl⟩
    | true =>
      let c : GaussianDirectPositions b := (bernoulliLeadingPairing b s hLeading).symm ⟨a, ha⟩
      refine ⟨c, Subtype.ext ?_⟩
      exact (bernoulli_leading_partner_spec b s hLeading a).1

theorem bernoulli_leading_direct_card_eq_entries {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) :
    Fintype.card (GaussianDirectPositions b) = bernoulliPatternEntryCount b s := by
  have h := Nat.card_eq_of_bijective _ (bernoulli_leading_direct_entry_bijective b s hLeading)
  rw [bernoulli_pattern_entry_range_card, Nat.card_eq_fintype_card] at h
  exact h

theorem bernoulli_leading_pairing_endpoint_eq {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s)
    (a : GaussianDirectPositions b) :
    Quotient.mk s a.val = Quotient.mk s
        (finRotate (k + 1) ((bernoulliLeadingPairing b s hLeading) a).val) ∧
      Quotient.mk s (finRotate (k + 1) a.val) =
        Quotient.mk s ((bernoulliLeadingPairing b s hLeading) a).val := by
  have h := (bernoulli_leading_partner_spec b s hLeading a.val).1
  change orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s)
    ((bernoulliLeadingPairing b s hLeading) a).val =
      orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) a.val at h
  simp only [orientedClosedWalkEntry, a.property,
    ((bernoulliLeadingPairing b s hLeading) a).property,
    Bool.false_eq_true, if_false, if_true, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

def bernoulliLeadingPairingQuotientMap {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) :
    Quotient (gaussianWordPairingSetoid b (finRotate (k + 1))
      (bernoulliLeadingPairing b s hLeading)) → Quotient s :=
  Quotient.lift (Quotient.mk s) (fun _ _ h => relation_coloring_eqv_gen _ _
    ((paired_walk_coloring_iff _ _ _ (Quotient.mk s)).mpr
      (bernoulli_leading_pairing_endpoint_eq b s hLeading)) h)

theorem bernoulli_leading_pairing_quotient_map_surjective {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) :
    Function.Surjective (bernoulliLeadingPairingQuotientMap b s hLeading) := by
  intro q
  induction q using Quotient.inductionOn with
  | h a => exact ⟨Quotient.mk _ a, rfl⟩

theorem bernoulli_leading_pairing_quotient_map_bijective {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) :
    Function.Bijective (bernoulliLeadingPairingQuotientMap b s hLeading) := by
  apply (bernoulli_leading_pairing_quotient_map_surjective b s hLeading).bijective_of_nat_card_le
  rw [gaussian_word_pairing_quotient_card]
  change gaussianWordVertexExponent b (finRotate (k + 1)) (bernoulliLeadingPairing b s hLeading) ≤
    bernoulliPatternVertexCount s
  rw [hLeading.2.1, ← bernoulli_leading_direct_card_eq_entries b s hLeading]
  exact gaussian_word_vertex_exponent_bound b _ _ (fin_rotate_same_cycle k)

theorem bernoulli_leading_pairing_setoid_eq {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) :
    gaussianWordPairingSetoid b (finRotate (k + 1)) (bernoulliLeadingPairing b s hLeading) = s := by
  apply Setoid.ext
  intro a c
  constructor
  · intro h
    exact Quotient.exact (congrArg (bernoulliLeadingPairingQuotientMap b s hLeading)
      (Quotient.sound h))
  · intro h
    exact Quotient.exact ((bernoulli_leading_pairing_quotient_map_bijective b s hLeading).1
      (show bernoulliLeadingPairingQuotientMap b s hLeading (Quotient.mk _ a) =
        bernoulliLeadingPairingQuotientMap b s hLeading (Quotient.mk _ c) from Quotient.sound h))

theorem bernoulli_leading_pairing_vertex_exponent {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) :
    gaussianWordVertexExponent b (finRotate (k + 1)) (bernoulliLeadingPairing b s hLeading) =
      Fintype.card (GaussianDirectPositions b) + 1 := by
  rw [← gaussian_word_pairing_quotient_card, bernoulli_leading_pairing_setoid_eq b s hLeading]
  change bernoulliPatternVertexCount s = _
  rw [hLeading.2.1, bernoulli_leading_direct_card_eq_entries b s hLeading]

end CircularLaw
