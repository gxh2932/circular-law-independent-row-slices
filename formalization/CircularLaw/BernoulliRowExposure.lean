import CircularLaw.ShiftedBernoulliUnitNormal
import CircularLaw.FiniteFreshProbabilityBound

/-!
# Exposing all but one Bernoulli row

The past and the omitted row are disjoint entry blocks. Reconstructing
the sample keeps the chosen leave-one-out normal independent of the fresh row.
-/

noncomputable section
open Classical

namespace CircularLaw

abbrev BernoulliRowPastIndex {n : ℕ} (i : Fin n) := {j : Fin n // j ≠ i} × Fin n

def bernoulliRowPastEmbedding {n : ℕ} (i : Fin n) :
    BernoulliRowPastIndex i ↪ Fin n × Fin n where
  toFun a := (a.1.val, a.2)
  inj' := by
    intro a b h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · exact congrArg (fun x : Fin n × Fin n => x.2) h

def bernoulliRowFreshEmbedding {n : ℕ} (i : Fin n) : Fin n ↪ Fin n × Fin n where
  toFun j := (i, j)
  inj' := by
    intro a b h
    exact congrArg Prod.snd h

theorem bernoulli_row_exposure_blocks_disjoint {n : ℕ} (i : Fin n)
    (a : BernoulliRowPastIndex i) (b : Fin n) :
    bernoulliRowPastEmbedding i a ≠ bernoulliRowFreshEmbedding i b := by
  intro h
  exact a.1.property (congrArg Prod.fst h)

def bernoulliRowPast {n : ℕ} (i : Fin n) (sample : BernoulliSquareSample n) :
    BernoulliRowPastIndex i → Bool := fun a => sample (bernoulliRowPastEmbedding i a)

def bernoulliRowFresh {n : ℕ} (i : Fin n) (sample : BernoulliSquareSample n) :
    Fin n → Bool := fun j => sample (bernoulliRowFreshEmbedding i j)

def bernoulliRowCompletion {n : ℕ} (i : Fin n)
    (past : BernoulliRowPastIndex i → Bool) (fresh : Fin n → Bool) :
    BernoulliSquareSample n :=
  fun a => if h : a.1 = i then fresh a.2 else past (⟨a.1, h⟩, a.2)

theorem bernoulli_row_completion_fresh {n : ℕ} (i : Fin n)
    (past : BernoulliRowPastIndex i → Bool) (fresh : Fin n → Bool) (j : Fin n) :
    bernoulliRowCompletion i past fresh (i, j) = fresh j := by
  simp [bernoulliRowCompletion]

theorem bernoulli_row_completion_past {n : ℕ} (i : Fin n)
    (past : BernoulliRowPastIndex i → Bool) (fresh : Fin n → Bool)
    (j : Fin n) (hji : j ≠ i) (k : Fin n) :
    bernoulliRowCompletion i past fresh (j, k) = past (⟨j, hji⟩, k) := by
  simp [bernoulliRowCompletion, hji]

theorem bernoulli_row_completion_reconstructs {n : ℕ}
    (i : Fin n) (sample : BernoulliSquareSample n) :
    bernoulliRowCompletion i (bernoulliRowPast i sample) (bernoulliRowFresh i sample) =
      sample := by
  ext ⟨j, k⟩
  by_cases hji : j = i
  · subst j
    simp [bernoulliRowCompletion, bernoulliRowFresh, bernoulliRowFreshEmbedding]
  · simp [bernoulliRowCompletion, hji, bernoulliRowPast, bernoulliRowPastEmbedding]

theorem bernoulli_row_completion_unit_normal_fresh_invariant {n : ℕ}
    (ζ : ℂ) (i : Fin n) (past : BernoulliRowPastIndex i → Bool)
    (fresh fresh' : Fin n → Bool) :
    shiftedBernoulliUnitNormal ζ (bernoulliRowCompletion i past fresh) i =
      shiftedBernoulliUnitNormal ζ (bernoulliRowCompletion i past fresh') i := by
  apply shifted_bernoulli_unit_normal_congr
  intro j hji k
  simp only [bernoulli_row_completion_past i past fresh j hji k,
    bernoulli_row_completion_past i past fresh' j hji k]

def bernoulliExposedUnitNormal {n : ℕ} (ζ : ℂ) (i : Fin n)
    (past : BernoulliRowPastIndex i → Bool) : EuclideanSpace ℂ (Fin n) :=
  shiftedBernoulliUnitNormal ζ (bernoulliRowCompletion i past (fun _ => false)) i

theorem bernoulli_unit_normal_eq_exposed {n : ℕ}
    (ζ : ℂ) (i : Fin n) (sample : BernoulliSquareSample n) :
    shiftedBernoulliUnitNormal ζ sample i =
      bernoulliExposedUnitNormal ζ i (bernoulliRowPast i sample) := by
  calc
    shiftedBernoulliUnitNormal ζ sample i = shiftedBernoulliUnitNormal ζ
        (bernoulliRowCompletion i (bernoulliRowPast i sample) (bernoulliRowFresh i sample)) i := by
      rw [bernoulli_row_completion_reconstructs]
    _ = bernoulliExposedUnitNormal ζ i (bernoulliRowPast i sample) :=
      bernoulli_row_completion_unit_normal_fresh_invariant ζ i _ _ _

end CircularLaw
