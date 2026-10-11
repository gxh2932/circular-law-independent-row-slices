import CircularLaw.ClosedWalkTreeOrientation
import CircularLaw.BernoulliPatternMeanLimits
import CircularLaw.GaussianWordPairingCounts

/-!
# The unique compatible partner in each Bernoulli leading pattern

Every entry of a leading pattern occurs exactly twice. The tree edge-cut
argument forces its two direct/adjoint flags to differ. Hence positions
have a unique opposite-flag partner, an involution, and the direct and
adjoint positions form an actual Gaussian-compatible bijection.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

local instance bernoulliLeadingPartnerBEq {α : Type*} (s : Setoid α) :
    BEq (Quotient s × Quotient s) := instBEqOfDecidableEq

theorem finite_fiber_two_eq_or {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (hCard : Fintype.card {a // P a} = 2) {a c : α} (ha : P a) (hc : P c) (hne : a ≠ c) :
    ∀ u, P u ↔ u = a ∨ u = c := by
  have hPair : ({a, c} : Finset α).card = 2 := by simp [hne]
  have hSub : ({a, c} : Finset α) ⊆ Finset.univ.filter P := by
    intro u hu
    rcases (show u = a ∨ u = c by simpa only [Finset.mem_insert, Finset.mem_singleton] using hu) with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  have hFilter : (Finset.univ.filter P).card = 2 := by
    simpa only [Fintype.card_subtype] using hCard
  have hEq : ({a, c} : Finset α) = Finset.univ.filter P :=
    Finset.eq_of_subset_of_card_le hSub (by rw [hPair, hFilter])
  intro u
  have hMem := congrArg (fun S : Finset α => u ∈ S) hEq
  simpa using (iff_of_eq hMem).symm

theorem bernoulli_leading_pattern_entry_fiber_card {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) (a : Fin (k + 1)) :
    Fintype.card {c // orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) c =
      orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) a} = 2 := by
  rw [← list_ofFn_count_eq_fiber_card]
  exact bernoulli_maximal_entry_pattern_paired b s hLeading.1 hLeading.2.2 _
    (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨a, rfl⟩))

theorem bernoulli_leading_pattern_opposite_entry {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) (a : Fin (k + 1)) :
    ∃ c, orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) c =
      orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) a ∧ b c ≠ b a := by
  apply closed_walk_maximal_opposite_entry _ b (Quotient.mk s) (fin_rotate_same_cycle k) _ a
  rw [bernoulli_pattern_quotient_range_card, bernoulli_pattern_entry_range_card]
  exact hLeading.2.1

theorem bernoulli_leading_pattern_unique_partner {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) (a : Fin (k + 1)) :
    ∃! c, orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) c =
      orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) a ∧ b c ≠ b a := by
  obtain ⟨c, he, hb⟩ := bernoulli_leading_pattern_opposite_entry b s hLeading a
  have hne : a ≠ c := fun h => hb (congrArg b h.symm)
  have hFiber := finite_fiber_two_eq_or
    (fun u => orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) u =
      orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) a)
    (bernoulli_leading_pattern_entry_fiber_card b s hLeading a) (a := a) (c := c) rfl he hne
  refine ⟨c, ⟨he, hb⟩, ?_⟩
  intro u hu
  rcases (hFiber u).mp hu.1 with rfl | h
  · exact False.elim (hu.2 rfl)
  · exact h

def bernoulliLeadingPartner {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) (a : Fin (k + 1)) :
    Fin (k + 1) := Classical.choose (bernoulli_leading_pattern_unique_partner b s hLeading a)

theorem bernoulli_leading_partner_spec {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) (a : Fin (k + 1)) :
    orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s)
        (bernoulliLeadingPartner b s hLeading a) =
      orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) a ∧
        b (bernoulliLeadingPartner b s hLeading a) ≠ b a :=
  (Classical.choose_spec (bernoulli_leading_pattern_unique_partner b s hLeading a)).1

theorem bernoulli_leading_partner_unique {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) (a c : Fin (k + 1))
    (he : orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) c =
      orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) a) (hb : b c ≠ b a) :
    c = bernoulliLeadingPartner b s hLeading a :=
  (Classical.choose_spec (bernoulli_leading_pattern_unique_partner b s hLeading a)).2 c ⟨he, hb⟩

theorem bernoulli_leading_partner_involution {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) :
    Function.Involutive (bernoulliLeadingPartner b s hLeading) := by
  intro a
  have h := bernoulli_leading_partner_spec b s hLeading a
  exact (bernoulli_leading_partner_unique b s hLeading
    (bernoulliLeadingPartner b s hLeading a) a h.1.symm (Ne.symm h.2)).symm

theorem bernoulli_leading_entry_fiber_iff {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) (a c : Fin (k + 1)) :
    orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) c =
      orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) a ↔
        c = a ∨ c = bernoulliLeadingPartner b s hLeading a := by
  have h := bernoulli_leading_partner_spec b s hLeading a
  exact finite_fiber_two_eq_or
    (fun u => orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) u =
      orientedClosedWalkEntry (finRotate (k + 1)) b (Quotient.mk s) a)
    (bernoulli_leading_pattern_entry_fiber_card b s hLeading a)
    (a := a) (c := bernoulliLeadingPartner b s hLeading a)
    rfl h.1 (fun he => h.2 (congrArg b he.symm)) c

def bernoulliLeadingPairing {k : ℕ} (b : Fin (k + 1) → Bool)
    (s : Setoid (Fin (k + 1))) (hLeading : BernoulliLeadingPattern b s) :
    GaussianWordPairing b where
  toFun a := ⟨bernoulliLeadingPartner b s hLeading a.val, by
    have h := (bernoulli_leading_partner_spec b s hLeading a.val).2
    rw [a.property] at h
    exact Bool.eq_true_of_not_eq_false h⟩
  invFun c := ⟨bernoulliLeadingPartner b s hLeading c.val, by
    have h := (bernoulli_leading_partner_spec b s hLeading c.val).2
    rw [c.property] at h
    exact Bool.eq_false_of_not_eq_true h⟩
  left_inv a := Subtype.ext (bernoulli_leading_partner_involution b s hLeading a.val)
  right_inv c := Subtype.ext (bernoulli_leading_partner_involution b s hLeading c.val)

end CircularLaw
