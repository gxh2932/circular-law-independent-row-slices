import CircularLaw.GraphLeadingKernel
import CircularLaw.BernoulliRestrictedUniqueExpansion

/-!
# The deterministic expansion seed at the exposure barrier

The integer barrier and the checked 4096 spread factor give a positive
seed (N-m)/32768+1. A graph budget at this seed covers every actual
leading kernel whose retained rank lies above the moving barrier.
-/

noncomputable section
open Classical
open scoped Matrix NNReal InnerProductSpace

namespace CircularLaw

def sourceExposureExpansionSeed (N m : ℕ) : ℕ := (N - m) / 32768 + 1

theorem source_exposure_expansion_seed_pos (N m : ℕ) :
    0 < sourceExposureExpansionSeed N m := by simp [sourceExposureExpansionSeed]

theorem source_exposure_seed_le_kernel_ceil {N m r : ℕ}
    (hGuard : (N - m) / 8 < m - r) :
    sourceExposureExpansionSeed N m ≤ Nat.ceil ((m - r : ℕ) / (4096 : ℝ)) := by
  unfold sourceExposureExpansionSeed
  apply Nat.succ_le_of_lt
  apply Nat.lt_ceil.mpr
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4096)).mpr
  have hNat : (N - m) / 32768 * 4096 < m - r := by omega
  exact_mod_cast hNat

theorem source_exposure_seed_le_leading_kernel {N r a m : ℕ}
    (A : Matrix (Fin a) (Fin m) ℂ) (h : r ≤ a)
    (hProd : leadingRowSingularProduct A h ≠ 0) (hGuard : (N - m) / 8 < m - r) :
    sourceExposureExpansionSeed N m ≤
      subspaceSpreadCoordinateCount (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin) := by
  rw [leading_kernel_spread_coordinate_count_eq A h hProd]
  exact source_exposure_seed_le_kernel_ceil hGuard

theorem matrix_unique_expansion_budget_mono_seed
    {ρ ι : Type*} [Fintype ρ] (A : Matrix ρ ι ℂ) (e : ρ ↪ ι)
    {β n d k k' u : ℝ} (hSeed : k ≤ k')
    (hBudget : MatrixUniqueExpansionBudget A e β n d k u) :
    MatrixUniqueExpansionBudget A e β n d k' u := by
  intro S hS hRange
  exact hBudget S (hSeed.trans hS) hRange

theorem source_exposure_unique_budget_for_leading_kernel {N r a m : ℕ}
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (z : ℂ)
    (h : r ≤ a) (hProd : leadingRowSingularProduct (diagonalEmbeddedShift A e z) h ≠ 0)
    (hGuard : (N - m) / 8 < m - r) {β d : ℝ}
    (hBudget : MatrixUniqueExpansionBudget A e β N d (sourceExposureExpansionSeed N m)
      (sourceGraphTerminalScale N d)) :
    MatrixUniqueExpansionBudget A e β N d
      (subspaceSpreadCoordinateCount
        (LinearMap.ker (leadingCompressedRows (diagonalEmbeddedShift A e z) h).toEuclideanLin))
      (sourceGraphTerminalScale N d) := by
  apply matrix_unique_expansion_budget_mono_seed A e _ hBudget
  exact_mod_cast source_exposure_seed_le_leading_kernel (diagonalEmbeddedShift A e z) h hProd hGuard

end CircularLaw
