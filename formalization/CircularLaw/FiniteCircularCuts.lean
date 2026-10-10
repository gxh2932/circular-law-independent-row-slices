import CircularLaw.GaussianMomentCycleBound

/-!
# A cyclic predicate with two switches is its exact circular interval

The side predicate is true at the first endpoint and false at the second.
It switches after each endpoint and is unchanged at all other successors.
The actual finite rotation therefore determines it uniquely, including
the wrap at the last position.
-/

noncomputable section
open Classical

namespace CircularLaw

def finiteCircularCut {n : ℕ} (i j v : Fin n) : Prop :=
  if i < j then v ≤ i ∨ j < v else j < v ∧ v ≤ i

theorem finite_circular_cut_start {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j) :
    finiteCircularCut i j i := by
  simp only [finiteCircularCut]
  split_ifs <;> omega

theorem finite_circular_cut_not_end {n : ℕ} (i j : Fin (n + 1)) :
    ¬finiteCircularCut i j j := by
  simp only [finiteCircularCut]
  split_ifs <;> omega

theorem finite_circular_cut_after_start {n : ℕ} (i j : Fin (n + 1)) :
    ¬finiteCircularCut i j (finRotate (n + 1) i) := by
  by_cases hLast : i = Fin.last n
  · subst i
    rw [finRotate_last]
    simp only [finiteCircularCut, Fin.le_def, Fin.lt_def, Fin.val_last, Fin.val_zero]
    split_ifs <;> omega
  · simp only [finiteCircularCut, Fin.le_def, Fin.lt_def, coe_finRotate_of_ne_last hLast]
    split_ifs <;> omega

theorem finite_circular_cut_after_end {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j) :
    finiteCircularCut i j (finRotate (n + 1) j) := by
  have hValNe : i.val ≠ j.val := fun h => hij (Fin.ext h)
  by_cases hLast : j = Fin.last n
  · subst j
    rw [finRotate_last]
    simp only [Fin.val_last] at hValNe
    simp only [finiteCircularCut, Fin.le_def, Fin.lt_def, Fin.val_last, Fin.val_zero]
    split_ifs <;> omega
  · simp only [finiteCircularCut, Fin.le_def, Fin.lt_def, coe_finRotate_of_ne_last hLast]
    split_ifs <;> omega

theorem finite_circular_cut_other_successor {n : ℕ} (i j v : Fin (n + 1))
    (hvi : v ≠ i) (hvj : v ≠ j) :
    finiteCircularCut i j (finRotate (n + 1) v) ↔ finiteCircularCut i j v := by
  have hviVal : v.val ≠ i.val := fun h => hvi (Fin.ext h)
  have hvjVal : v.val ≠ j.val := fun h => hvj (Fin.ext h)
  by_cases hLast : v = Fin.last n
  · subst v
    rw [finRotate_last]
    simp only [Fin.val_last] at hviVal hvjVal
    simp only [finiteCircularCut, Fin.le_def, Fin.lt_def, Fin.val_last, Fin.val_zero]
    split_ifs <;> omega
  · simp only [finiteCircularCut, Fin.le_def, Fin.lt_def, coe_finRotate_of_ne_last hLast]
    split_ifs <;> omega

theorem cyclic_predicate_eq_of_successor_agreement {α : Type*} (ρ : Equiv.Perm α)
    (P Q : α → Prop) (hOrbit : ∀ v w, ρ.SameCycle v w) (i : α)
    (hBase : P i ↔ Q i)
    (hStep : ∀ v, (P (ρ v) ↔ Q (ρ v)) ↔ (P v ↔ Q v)) :
    ∀ v, P v ↔ Q v := by
  intro v
  have hEq : ∀ v, (P (ρ v) ↔ Q (ρ v)) = (P v ↔ Q v) := fun v => propext (hStep v)
  have h := permutation_invariant_same_cycle ρ (fun v => P v ↔ Q v) hEq (hOrbit i v)
  change (P i ↔ Q i) = (P v ↔ Q v) at h
  exact h ▸ hBase

theorem finite_circular_cut_eq_of_two_switches {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j)
    (P : Fin (n + 1) → Prop) (hStart : P i) (hEnd : ¬P j)
    (hAfterStart : ¬P (finRotate (n + 1) i)) (hAfterEnd : P (finRotate (n + 1) j))
    (hOther : ∀ v, v ≠ i → v ≠ j → (P (finRotate (n + 1) v) ↔ P v)) :
    ∀ v, P v ↔ finiteCircularCut i j v := by
  apply cyclic_predicate_eq_of_successor_agreement (finRotate (n + 1)) P
    (finiteCircularCut i j) (fin_rotate_same_cycle n) i
  · exact iff_of_true hStart (finite_circular_cut_start i j hij)
  · intro v
    by_cases hvi : v = i
    · subst v
      have hQ := finite_circular_cut_start i j hij
      have hQAfter := finite_circular_cut_after_start i j
      tauto
    · by_cases hvj : v = j
      · subst v
        have hQ := finite_circular_cut_not_end i j
        have hQAfter := finite_circular_cut_after_end i j hij
        tauto
      · rw [hOther v hvi hvj, finite_circular_cut_other_successor i j v hvi hvj]

end CircularLaw
