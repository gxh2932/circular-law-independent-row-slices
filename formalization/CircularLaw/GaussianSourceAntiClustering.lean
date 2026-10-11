import CircularLaw.GaussianSourceParameters

/-!
# Gaussian source conclusion once the exceptional set has the required size

The literal parameters close the averaging and radius-absorption part of
the manuscript proposition. Only the deterministic size bound for the
constructed exceptional set remains a premise of the final assembly.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem gaussianSourceGrowth_ratio (n L : ℕ) :
    gaussianSourceGrowth ((L : ℝ) / n) = structuralGrowth n L := by
  unfold gaussianSourceGrowth structuralGrowth
  congr 1
  simp [div_eq_mul_inv]

theorem gaussianSourceBeta_ratio (n L : ℕ) :
    gaussianSourceBeta ((L : ℝ) / n) = (1 / 4 : ℝ) * ((L : ℝ) / (4 * n)) ^ 3 := by
  unfold gaussianSourceBeta
  congr 2
  ring

def sourceGaussianExceptional {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (L : ℕ) (CG : ℝ) : Finset (Fin n) :=
  projectedGaussianExceptional E (gaussianSourceAlpha_pos CG ((L : ℝ) / n))
    (gaussianSourceBeta_nonneg (div_nonneg (Nat.cast_nonneg L) (Nat.cast_nonneg n))) (L / 2)

def GaussianAntiClusterEvent {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (L : ℕ) (C : ℝ)
    (z : Fin n → ℂ) : Prop :=
  ∃ J : Finset (Fin n), (J.card : ℝ) ≤ 2 * n * structuralClusterFraction n L ∧
    ∀ w : ℂ, ((Finset.univ \ J).filter
      (fun j => ‖projectedComplexGaussian E z j - w‖ ≤
        Real.exp (-C * structuralGrowth n L))).card ≤ L

theorem GaussianAntiClusterEvent_measurableSet {n : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (L : ℕ) (C : ℝ) :
    MeasurableSet {z | GaussianAntiClusterEvent E L C z} := by
  have hContinuous (j : Fin n) : Continuous (fun z => projectedComplexGaussian E z j) :=
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp
      (projectedComplexGaussian_continuous E)
  have hEq : {z | GaussianAntiClusterEvent E L C z} =
      ⋃ J : Finset (Fin n),
        {z | (J.card : ℝ) ≤ 2 * n * structuralClusterFraction n L ∧
          ∀ w : ℂ, ((Finset.univ \ J).filter
          (fun j => ‖projectedComplexGaussian E z j - w‖ ≤
            Real.exp (-C * structuralGrowth n L))).card ≤ L} := by
    ext z
    simp only [GaussianAntiClusterEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hEq]
  apply MeasurableSet.iUnion
  intro J
  by_cases hJ : (J.card : ℝ) ≤ 2 * n * structuralClusterFraction n L
  · simpa only [hJ, true_and] using coordinate_all_disks_card_measurableSet
      (fun z j => projectedComplexGaussian E z j) hContinuous (Finset.univ \ J) L
      (Real.exp (-C * structuralGrowth n L))
  · simp only [hJ, false_and, Set.setOf_false]
    exact MeasurableSet.empty

theorem sourceGaussian_anti_cluster_greedy_success {n L : ℕ} (hn : 0 < n)
    (hL : 2 ≤ L) (hLn : L ≤ n)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (CG : ℝ) :
    1 - (9 / 8 : ℝ) * ((L : ℝ) / n) ≤ (standardComplexGaussianVectorLaw n).real
      {z | ∀ w : ℂ, ((Finset.univ \ sourceGaussianExceptional E L CG).filter
        (fun j => ‖projectedComplexGaussian E z j - w‖ ≤
          Real.exp (-(CG + 1024) * structuralGrowth n L))).card ≤ L} := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLR : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have ht : 0 < (L : ℝ) / n := div_pos hLR hnR
  have ht1 : (L : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hLn)
  obtain ⟨hb, h2b, _⟩ := gaussianSource_half_cutoff hL
  have hRadius := gaussianSource_radius_absorption ht ht1 CG
  rw [gaussianSourceGrowth_ratio] at hRadius
  have hGood := projectedGaussian_greedy_anti_cluster_card_le hb h2b E
    (gaussianSourceAlpha_pos CG ((L : ℝ) / n)) (gaussianSourceBeta_pos ht)
    (gaussianSourceBeta_lt_one ht ht1) (gaussianSourceSmallBall_pos ht).le hRadius
  have hFailure := gaussianSource_failure_bound hn hL
  exact (sub_le_sub_left hFailure 1).trans hGood

theorem sourceGaussian_anti_cluster_of_exceptional_bound {n L : ℕ} (hn : 0 < n)
    (hL : 2 ≤ L) (hLn : L ≤ n)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) {CG : ℝ} (hCG : 0 ≤ CG)
    (hSize : ((sourceGaussianExceptional E L CG).card : ℝ) ≤
      2 * n * structuralClusterFraction n L) :
    1 - (CG + 1024) * ((L : ℝ) / n) ≤
      (standardComplexGaussianVectorLaw n).real {z | GaussianAntiClusterEvent E L (CG + 1024) z} := by
  have hConst : (9 / 8 : ℝ) ≤ CG + 1024 := by linarith
  have hRatio : 0 ≤ (L : ℝ) / n := div_nonneg (Nat.cast_nonneg L) (Nat.cast_nonneg n)
  apply (sub_le_sub_left (mul_le_mul_of_nonneg_right hConst hRatio) 1).trans
  apply (sourceGaussian_anti_cluster_greedy_success hn hL hLn E CG).trans
  exact measureReal_mono (fun _ hz => ⟨sourceGaussianExceptional E L CG, hSize, hz⟩)

end CircularLaw
