import CircularLaw.GaussianSourceRange
import CircularLaw.GaussianGreedyCopyClusters

/-!
# The forbidden-vector contradiction for the actual greedy exceptional set

Uniform lower and upper coordinate bounds, and the actual copy-closeness
event, produce a nonzero normal vector with all reverse-steepness
inequalities and a forbidden disk. The structural alternatives therefore
bound the deterministic exceptional set.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory

namespace CircularLaw

def FixedSubspaceStructural {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (L q : ℕ) : Prop :=
  ∀ v : EuclideanSpace ℂ (Fin n), v ≠ 0 → v ∈ Eᗮ →
    (∃ i : ℕ, 0 < i ∧ i ≤ q ∧
      (9 / 10 : ℝ) * ((n : ℝ) / i) ^ 3 * orderedNormAt (fun j => v j) q <
        orderedNormAt (fun j => v j) i) ∨
    (∀ i : ℕ, 0 < i → i ≤ q → orderedNormAt (fun j => v j) i ≤
      (9 / 10 : ℝ) * ((n : ℝ) / i) ^ 3 * orderedNormAt (fun j => v j) q) ∧
    ∀ w : ℂ, ((Finset.univ.filter (fun j => ‖v j - w‖ ≤
      Real.exp (-2 * structuralGrowth n L) * orderedNormAt (fun j => v j) q)).card : ℝ) ≤
        n * structuralClusterFraction n L

theorem sourceGaussianCopyCount_pos_of_exceptional_nonempty {n L : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (C : ℝ)
    (hJ : (sourceGaussianExceptional E L C).Nonempty) :
    0 < sourceGaussianCopyCount E L C := by
  let R := projectedGaussianStronglyCorrelated E (gaussianSourceAlpha C ((L : ℝ) / n))
    (gaussianSourceBeta ((L : ℝ) / n))
  let hR := projectedGaussianStronglyCorrelated_refl E
    (gaussianSourceAlpha_pos C ((L : ℝ) / n))
    (gaussianSourceBeta_nonneg (div_nonneg (Nat.cast_nonneg L) (Nat.cast_nonneg n)))
  obtain ⟨j, hj⟩ := hJ
  obtain ⟨k, _⟩ := greedyCorrelationExceptional_mem_stage R hR (L / 2) hj
  exact (Nat.zero_le k.val).trans_lt k.isLt

theorem sourceGaussianCopyCount_le_dimension {n L : ℕ}
    (hn : 0 < n) (hL : 2 ≤ L) (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (C : ℝ) :
    sourceGaussianCopyCount E L C ≤ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLPos : 0 < L := by omega
  have hLPosR : (0 : ℝ) < L := by linarith
  have hCap : 2 * (n : ℝ) / L ≤ n := (div_le_iff₀ hLPosR).mpr (by nlinarith)
  exact_mod_cast (sourceGaussianGreedyCopy_count_bound hLPos E C).trans hCap

theorem sourceGaussian_exceptional_size_of_success_sample {n L q : ℕ}
    (hn : 64 ≤ n) (hL : 131072 ≤ L) (hLn : L ≤ n) (hq : 0 < q)
    (hqSmall : q ≤ L / 2048) (hLog : Real.log (n : ℝ) ≤ (n : ℝ) / L)
    (hRatio : 12288 ≤ (n : ℝ) / L)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {C : ℝ} (hC : 8192 ≤ C)
    (hStructural : FixedSubspaceStructural E L q)
    (z : Fin (sourceGaussianCopyCount E L C) → (Fin n → ℂ))
    (hFar : ((sourceGaussianFarCoordinates E L C z).card : ℝ) <
      ((sourceGaussianExceptional E L C).card : ℝ) / 2)
    (hNonflat : ∀ x : EuclideanSpace ℂ (Fin (sourceGaussianCopyCount E L C)), ‖x‖ = 1 →
      (L : ℝ) / (2048 * n) < orderedNormAt
        (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i) (L / 2048) ∧
      gaussianCopiesCombination (projectedGaussianCopies E z) x ≠ 0)
    (hUpper : ∀ x : EuclideanSpace ℂ (Fin (sourceGaussianCopyCount E L C)), ‖x‖ ≤ 1 →
      ∀ i : Fin n, ‖gaussianCopiesCombination (projectedGaussianCopies E z) x i‖ ≤
        Real.sqrt (sourceGaussianCopyCount E L C) *
          Real.sqrt (Real.log ((sourceGaussianCopyCount E L C : ℝ) * n / (1 / 64)))) :
    ((sourceGaussianExceptional E L C).card : ℝ) ≤ 2 * n * structuralClusterFraction n L := by
  by_contra hSize
  have hTooLarge : 2 * n * structuralClusterFraction n L <
      ((sourceGaussianExceptional E L C).card : ℝ) := lt_of_not_ge hSize
  have hCutoffNonneg : 0 ≤ 2 * (n : ℝ) * structuralClusterFraction n L := by
    unfold structuralClusterFraction
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hCardPosR : (0 : ℝ) < (sourceGaussianExceptional E L C).card :=
    hCutoffNonneg.trans_lt hTooLarge
  have hJ : (sourceGaussianExceptional E L C).Nonempty := Finset.card_pos.mp (by exact_mod_cast hCardPosR)
  have hnPos : 0 < n := by omega
  have hLPos : 0 < L := by omega
  have hpPos := sourceGaussianCopyCount_pos_of_exceptional_nonempty E C hJ
  have hpCount := sourceGaussianGreedyCopy_count_bound hLPos E C
  have hpCount' : (sourceGaussianCopyCount E L C : ℝ) ≤ 2 * ((n : ℝ) / L) := by
    convert hpCount using 1
    ring
  have hCap := gaussianUniformCoordinate_log_cap hn hpPos
    (sourceGaussianCopyCount_le_dimension hnPos (by omega) E C) hpCount' hLog hRatio
  obtain ⟨x, hx, hOrthogonal, w, hDisk⟩ := gaussianGreedyCopy_unit_cluster_on_success E
    (gaussianSourceAlpha_pos C ((L : ℝ) / n))
    (gaussianSourceBeta_nonneg (div_nonneg (Nat.cast_nonneg L) (Nat.cast_nonneg n)))
    (L / 2) hJ z hFar
  let v := gaussianCopiesCombination (projectedGaussianCopies E z) x
  have hLow := hNonflat x hx
  have hCoords : ∀ j : Fin n, ‖v j‖ ≤ ((n : ℝ) / L) ^ 2 / 4096 :=
    fun j => (hUpper x hx.le j).trans hCap
  have hrn : L / 2048 ≤ n := by omega
  have hReverse := gaussianForbidden_reverse_from_coordinate_bounds hnPos hLPos hq hqSmall hrn
    (by omega : q ≤ L) (fun j => v j) hLow.1.le hCoords
  have hLowQ : (L : ℝ) / (2048 * n) ≤ orderedNormAt (fun j => v j) q :=
    hLow.1.le.trans (orderedNormAt_antitone (fun j => v j) hq hqSmall hrn)
  have hRadius := sourceGaussian_combination_radius_absorption hnPos hLPos hLn hC hpCount
  have hRadiusQ : (sourceGaussianCopyCount E L C : ℝ) * gaussianSourceAlpha C ((L : ℝ) / n) ≤
      Real.exp (-2 * structuralGrowth n L) * orderedNormAt (fun j => v j) q :=
    hRadius.trans (mul_le_mul_of_nonneg_left hLowQ (Real.exp_pos _).le)
  have hCard : (((sourceGaussianExceptional E L C).filter
      (fun j => ‖v j - w‖ ≤ (sourceGaussianCopyCount E L C : ℝ) *
        gaussianSourceAlpha C ((L : ℝ) / n))).card : ℝ) ≤
      ((Finset.univ.filter (fun j => ‖v j - w‖ ≤ Real.exp (-2 * structuralGrowth n L) *
        orderedNormAt (fun j => v j) q)).card : ℝ) := by
    have hSubset : (sourceGaussianExceptional E L C).filter
        (fun j => ‖v j - w‖ ≤ (sourceGaussianCopyCount E L C : ℝ) *
          gaussianSourceAlpha C ((L : ℝ) / n)) ⊆
        Finset.univ.filter (fun j => ‖v j - w‖ ≤ Real.exp (-2 * structuralGrowth n L) *
          orderedNormAt (fun j => v j) q) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2.trans hRadiusQ⟩
    exact_mod_cast Finset.card_le_card hSubset
  have hViolation : (n : ℝ) * structuralClusterFraction n L <
      ((Finset.univ.filter (fun j => ‖v j - w‖ ≤ Real.exp (-2 * structuralGrowth n L) *
        orderedNormAt (fun j => v j) q)).card : ℝ) := by
    have hHalf : (n : ℝ) * structuralClusterFraction n L <
        ((sourceGaussianExceptional E L C).card : ℝ) / 2 := by linarith
    exact (hHalf.trans hDisk).trans_le hCard
  rcases hStructural v hLow.2 hOrthogonal with hSteep | ⟨_, hClusters⟩
  · obtain ⟨i, hi, hiq, hStrict⟩ := hSteep
    exact (not_lt_of_ge (hReverse i hi hiq)) hStrict
  · exact (not_lt_of_ge (hClusters w)) hViolation

end CircularLaw
