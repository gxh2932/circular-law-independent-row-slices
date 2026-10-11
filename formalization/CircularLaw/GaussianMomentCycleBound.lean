import CircularLaw.GaussianPairingCycleCounts
import CircularLaw.PermutationCycleGraph
import Mathlib.GroupTheory.Perm.Fin

/-!
# Every Gaussian Gram pairing has the correct dimension exponent

The product of the matching and row permutations is the actual cyclic
successor. Its transitivity makes the cycle incidence graph connected.
The sum of the two cycle counts is therefore at most `order+1`.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem fin_rotate_same_cycle (k : ℕ) (a b : Fin (k + 1)) :
    (finRotate (k + 1)).SameCycle a b := by
  cases k with
  | zero =>
    have hab : a = b := by apply Fin.ext; omega
    exact hab.sameCycle _
  | succ k =>
    apply (isCycle_finRotate (n := k)).sameCycle
    · exact Equiv.Perm.mem_support.mp (by rw [support_finRotate]; exact Finset.mem_univ _)
    · exact Equiv.Perm.mem_support.mp (by rw [support_finRotate]; exact Finset.mem_univ _)

def gaussianGramCycleExponent (k : ℕ) (σ : Equiv.Perm (Fin (k + 1))) : ℕ :=
  permutationCycleCount σ + permutationCycleCount (finRotate (k + 1) * σ⁻¹)

theorem gaussian_gram_cycle_exponent_bound (k : ℕ) (σ : Equiv.Perm (Fin (k + 1))) :
    gaussianGramCycleExponent k σ ≤ k + 2 := by
  have hOrbit (a b : Fin (k + 1)) :
      ((finRotate (k + 1) * σ⁻¹) * σ).SameCycle a b := by
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using fin_rotate_same_cycle k a b
  have h := permutation_cycle_count_product_bound σ (finRotate (k + 1) * σ⁻¹) hOrbit
  simpa only [gaussianGramCycleExponent, Fintype.card_fin] using h

def gaussianLeadingMomentCount (k : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin (k + 1)) // gaussianGramCycleExponent k σ = k + 2}

theorem gaussian_leading_moment_count_le_factorial (k : ℕ) :
    gaussianLeadingMomentCount k ≤ (k + 1).factorial := by
  have h := Fintype.card_subtype_le
    (fun σ : Equiv.Perm (Fin (k + 1)) => gaussianGramCycleExponent k σ = k + 2)
  simpa only [gaussianLeadingMomentCount, Fintype.card_perm, Fintype.card_fin] using h

end CircularLaw
