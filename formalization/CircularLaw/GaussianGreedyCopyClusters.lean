import CircularLaw.GaussianCombinationClusters
import CircularLaw.GaussianSourceAntiClustering

/-!
# Large clusters in combinations of the actual greedy Gaussian copies

The actual representative lookup discharges every marginal correlation
premise. A measurable success event has probability at least `1-2*p*beta`.
On that event a unit combination in the original orthogonal complement
has a disk containing more than half the actual exceptional set. This
does not supply non-flatness or non-steepness of the combination.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

def gaussianGreedyCopyCount {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) (b : ℕ) : ℕ :=
  greedyCorrelationStop (projectedGaussianStronglyCorrelated E α β)
    (projectedGaussianStronglyCorrelated_refl E hα hβ) b

def gaussianGreedyRepresentativeAt {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) (b : ℕ) : Fin n → Fin n :=
  greedyCorrelationRepresentativeAt (projectedGaussianStronglyCorrelated E α β)
    (projectedGaussianStronglyCorrelated_refl E hα hβ) b

def gaussianGreedyFarCoordinates {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) (b : ℕ)
    (z : Fin (gaussianGreedyCopyCount E hα hβ b) → (Fin n → ℂ)) : Finset (Fin n) :=
  copyFarCoordinates (projectedGaussianExceptional E hα hβ b)
    (gaussianGreedyRepresentativeAt E hα hβ b)
    (fun k j => projectedGaussianCopies E z k j) α

theorem gaussianGreedyCopy_success {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) (b : ℕ)
    (hJ : (projectedGaussianExceptional E hα hβ b).Nonempty) :
    MeasurableSet {z | ((gaussianGreedyFarCoordinates E hα hβ b z).card : ℝ) <
      ((projectedGaussianExceptional E hα hβ b).card : ℝ) / 2} ∧
      1 - 2 * (gaussianGreedyCopyCount E hα hβ b : ℝ) * β ≤
        (standardGaussianCopiesLaw n (gaussianGreedyCopyCount E hα hβ b)).real
          {z | ((gaussianGreedyFarCoordinates E hα hβ b z).card : ℝ) <
            ((projectedGaussianExceptional E hα hβ b).card : ℝ) / 2} := by
  apply copyFarCoordinates_half_success
    (standardGaussianCopiesLaw n (gaussianGreedyCopyCount E hα hβ b))
    (projectedGaussianExceptional E hα hβ b) hJ _ _ α β
  · intro k j
    exact ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp
      (projectedGaussianCopies_continuous E k)).measurable
  · intro k j hj
    rw [projectedGaussianCopies_pair_tail]
    exact (projectedGaussianStronglyCorrelated_symm E α β _ j).mp
      (greedyCorrelationRepresentativeAt_related (projectedGaussianStronglyCorrelated E α β)
        (projectedGaussianStronglyCorrelated_refl E hα hβ) b j hj)

theorem gaussianGreedyCopy_unit_cluster_on_success {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) (b : ℕ)
    (hJ : (projectedGaussianExceptional E hα hβ b).Nonempty)
    (z : Fin (gaussianGreedyCopyCount E hα hβ b) → (Fin n → ℂ))
    (hFar : ((gaussianGreedyFarCoordinates E hα hβ b z).card : ℝ) <
      ((projectedGaussianExceptional E hα hβ b).card : ℝ) / 2) :
    ∃ x : EuclideanSpace ℂ (Fin (gaussianGreedyCopyCount E hα hβ b)), ‖x‖ = 1 ∧
      gaussianCopiesCombination (fun k => projectedGaussianCopies E z k) x ∈ Eᗮ ∧
      ∃ w : ℂ, ((projectedGaussianExceptional E hα hβ b).card : ℝ) / 2 <
        (((projectedGaussianExceptional E hα hβ b).filter
          (fun j => ‖gaussianCopiesCombination (fun k => projectedGaussianCopies E z k) x j - w‖ ≤
            (gaussianGreedyCopyCount E hα hβ b : ℝ) * α)).card : ℝ) := by
  let R := projectedGaussianStronglyCorrelated E α β
  let hR := projectedGaussianStronglyCorrelated_refl E hα hβ
  obtain ⟨j, hj⟩ := hJ
  obtain ⟨k, _⟩ := greedyCorrelationExceptional_mem_stage R hR b hj
  have hp : 0 < gaussianGreedyCopyCount E hα hβ b := (Nat.zero_le k.val).trans_lt k.isLt
  obtain ⟨x, hx, w, hEqual⟩ := gaussianRepresentative_unit_combination_of_pos hp
    (fun k => projectedGaussianCopies E z k) (greedyCorrelationRepresentative R hR b)
  refine ⟨x, hx, gaussianCopiesCombination_mem_submodule Eᗮ _
    (fun k => projectedComplexGaussian_mem_orthogonal E (z k)) x, w, ?_⟩
  apply gaussianCopiesCombination_large_cluster
    (projectedGaussianExceptional E hα hβ b) (gaussianGreedyRepresentativeAt E hα hβ b)
    (fun k => projectedGaussianCopies E z k) x hx.le w α _ hFar
  intro j hj
  exact greedyCorrelationRepresentativeAt_common_value R hR b
    (fun j => gaussianCopiesCombination (fun k => projectedGaussianCopies E z k) x j)
    w hEqual j hj

theorem sourceGaussianGreedyCopy_count_bound {n L : ℕ} (hL : 0 < L)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (CG : ℝ) :
    (gaussianGreedyCopyCount E (gaussianSourceAlpha_pos CG ((L : ℝ) / n))
      (gaussianSourceBeta_nonneg (div_nonneg (Nat.cast_nonneg L) (Nat.cast_nonneg n)))
        (L / 2) : ℝ) ≤ 2 * n / L := by
  let R := projectedGaussianStronglyCorrelated E (gaussianSourceAlpha CG ((L : ℝ) / n))
    (gaussianSourceBeta ((L : ℝ) / n))
  let hR := projectedGaussianStronglyCorrelated_refl E
    (gaussianSourceAlpha_pos CG ((L : ℝ) / n))
    (gaussianSourceBeta_nonneg (div_nonneg (Nat.cast_nonneg L) (Nat.cast_nonneg n)))
  have hStop := greedyCorrelationStop_mul_le_dimension R hR (L / 2)
  have hFloor : L ≤ 2 * (L / 2 + 1) := by omega
  have hNat : greedyCorrelationStop R hR (L / 2) * L ≤ 2 * n := by
    calc
      _ ≤ greedyCorrelationStop R hR (L / 2) * (2 * (L / 2 + 1)) :=
        Nat.mul_le_mul_left _ hFloor
      _ = 2 * (greedyCorrelationStop R hR (L / 2) * (L / 2 + 1)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hStop
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  apply (le_div_iff₀ hLR).mpr
  exact_mod_cast hNat

theorem sourceGaussianGreedyCopy_failure_bound {n L : ℕ} (hn : 0 < n) (hL : 0 < L) (hLn : L ≤ n)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (CG : ℝ) :
    2 * (gaussianGreedyCopyCount E (gaussianSourceAlpha_pos CG ((L : ℝ) / n))
      (gaussianSourceBeta_nonneg (div_nonneg (Nat.cast_nonneg L) (Nat.cast_nonneg n)))
        (L / 2) : ℝ) *
        gaussianSourceBeta ((L : ℝ) / n) ≤ 1 / 64 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hCount := sourceGaussianGreedyCopy_count_bound hL E CG
  have hBeta := gaussianSourceBeta_nonneg (div_nonneg hLR.le hnR.le)
  have hRatio : (L : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hLn)
  have hSq : ((L : ℝ) / n) ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (div_nonneg hLR.le hnR.le) hRatio 2
  calc
    _ ≤ 2 * (2 * n / L) * gaussianSourceBeta ((L : ℝ) / n) := by
      gcongr
    _ = (1 / 64 : ℝ) * ((L : ℝ) / n) ^ 2 := by
      unfold gaussianSourceBeta
      field_simp
      ring
    _ ≤ _ := by linarith only [hSq]

def sourceGaussianCopyCount {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (L : ℕ) (CG : ℝ) : ℕ :=
  gaussianGreedyCopyCount E (gaussianSourceAlpha_pos CG ((L : ℝ) / n))
    (gaussianSourceBeta_nonneg (div_nonneg (Nat.cast_nonneg L) (Nat.cast_nonneg n))) (L / 2)

def sourceGaussianFarCoordinates {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (L : ℕ) (CG : ℝ)
    (z : Fin (sourceGaussianCopyCount E L CG) → (Fin n → ℂ)) : Finset (Fin n) :=
  gaussianGreedyFarCoordinates E (gaussianSourceAlpha_pos CG ((L : ℝ) / n))
    (gaussianSourceBeta_nonneg (div_nonneg (Nat.cast_nonneg L) (Nat.cast_nonneg n))) (L / 2) z

theorem sourceGaussianGreedyCopy_success {n L : ℕ} (hn : 0 < n) (hL : 0 < L) (hLn : L ≤ n)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (CG : ℝ)
    (hJ : (sourceGaussianExceptional E L CG).Nonempty) :
    MeasurableSet {z | ((sourceGaussianFarCoordinates E L CG z).card : ℝ) <
      ((sourceGaussianExceptional E L CG).card : ℝ) / 2} ∧
      (63 / 64 : ℝ) ≤ (standardGaussianCopiesLaw n (sourceGaussianCopyCount E L CG)).real
        {z | ((sourceGaussianFarCoordinates E L CG z).card : ℝ) <
          ((sourceGaussianExceptional E L CG).card : ℝ) / 2} := by
  have hGood := gaussianGreedyCopy_success E (gaussianSourceAlpha_pos CG ((L : ℝ) / n))
    (gaussianSourceBeta_nonneg (div_nonneg (Nat.cast_nonneg L) (Nat.cast_nonneg n))) (L / 2) hJ
  have hFailure := sourceGaussianGreedyCopy_failure_bound hn hL hLn E CG
  refine ⟨hGood.1, ?_⟩
  apply le_trans _ hGood.2
  linarith only [hFailure]

end CircularLaw
