import CircularLaw.EqualBlockWitnessNorm
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Decreasing coordinate norms

Sorting the negatives of the coordinate norms gives a permutation of the
actual coordinates, including ties. Rank zero is the manuscript's first
order statistic.
-/

noncomputable section
open Classical

namespace CircularLaw

def normOrderPerm {n : ℕ} (y : Fin n → ℂ) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => -‖y i‖)

def orderedNorm {n : ℕ} (y : Fin n → ℂ) (i : Fin n) : ℝ :=
  ‖y (normOrderPerm y i)‖

theorem orderedNorm_antitone {n : ℕ} (y : Fin n → ℂ) : Antitone (orderedNorm y) := by
  intro i j hij
  have h := Tuple.monotone_sort (fun i => -‖y i‖) hij
  exact neg_le_neg_iff.mp h

theorem orderedNorm_nonneg {n : ℕ} (y : Fin n → ℂ) (i : Fin n) :
    0 ≤ orderedNorm y i := norm_nonneg _

theorem orderedNorm_of_rank {n : ℕ} (y : Fin n → ℂ) (i : Fin n) :
    orderedNorm y ((normOrderPerm y).symm i) = ‖y i‖ := by
  simp only [orderedNorm, Equiv.apply_symm_apply]

end CircularLaw
