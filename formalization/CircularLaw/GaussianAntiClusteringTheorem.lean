import CircularLaw.GaussianExceptionalContradiction
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The full fixed-subspace Gaussian anti-clustering proposition

Three actual measurable success events have a common sample. The checked
forbidden-vector argument bounds the deterministic exceptional set. The
previous Gaussian averaging theorem then gives the full named conclusion
in the standing manuscript band, with absolute constants and uniform n.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem gaussian_three_success_sets_common_point {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (A B D : Set X)
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hAProb : (63 / 64 : ℝ) ≤ μ.real A) (hBProb : (63 / 64 : ℝ) ≤ μ.real B)
    (hDProb : (63 / 64 : ℝ) ≤ μ.real D) : (A ∩ B ∩ D).Nonempty := by
  have hAB := measureReal_union_add_inter (μ := μ) (s := A) hB
    (measure_ne_top μ A) (measure_ne_top μ B)
  have hUnionAB : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
  have hABProb : (62 / 64 : ℝ) ≤ μ.real (A ∩ B) := by linarith
  have hABD := measureReal_union_add_inter (μ := μ) (s := A ∩ B) hD
    (measure_ne_top μ (A ∩ B)) (measure_ne_top μ D)
  have hUnionABD : μ.real ((A ∩ B) ∪ D) ≤ 1 := measureReal_le_one
  have hPositive : 0 < μ.real (A ∩ B ∩ D) := by linarith
  exact nonempty_of_measureReal_ne_zero hPositive.ne'

theorem gaussianNonflat_large_dimension_failure {L : ℕ} (hL : 131072 ≤ L) :
    Real.exp (-(L : ℝ) / 2048) ≤ 1 / 64 := by
  have hLR : (131072 : ℝ) ≤ L := by exact_mod_cast hL
  have hExp : (64 : ℝ) ≤ Real.exp ((L : ℝ) / 2048) := by
    linarith [Real.add_one_le_exp ((L : ℝ) / 2048)]
  rw [show -(L : ℝ) / 2048 = -((L : ℝ) / 2048) by ring, Real.exp_neg, inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hExp

theorem eventually_sourceGaussian_exceptional_size_uniform {a C : ℝ}
    (ha : 0 < a) (haSmall : a ≤ 1 / 2048) (hC : 1 ≤ C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, (n : ℝ) / (Real.log (n : ℝ)) ^ 288 ≤ L →
        (L : ℝ) ≤ (n : ℝ) / (d : ℝ) ^ 3 →
        ∀ E : Submodule ℂ (EuclideanSpace ℂ (Fin n)), L ≤ Module.finrank ℂ Eᗮ →
          FixedSubspaceStructural E L (sourceNormalRank a L) →
          ((sourceGaussianExceptional E L 8192).card : ℝ) ≤
            2 * n * structuralClusterFraction n L := by
  filter_upwards [eventually_sourceGaussian_ranges_uniform ha haSmall hC σ,
    eventually_projectedGaussianCopies_uniform_nonflat_success] with n hRanges hNonflat
  intro d hBand L hLower hUpper E hm hStructural
  obtain ⟨hn, hL, hLn, hSqrt, hCopies, hLogRatio, hRatioLarge, hq, hqSmall⟩ :=
    hRanges d hBand L hLower hUpper
  have hnPos : 0 < n := by omega
  have hLPos : 0 < L := by omega
  have hCutoffNonneg : 0 ≤ 2 * (n : ℝ) * structuralClusterFraction n L := by
    unfold structuralClusterFraction
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  by_cases hJ : (sourceGaussianExceptional E L 8192).Nonempty
  · have hpPos := sourceGaussianCopyCount_pos_of_exceptional_nonempty E 8192 hJ
    have hpCount := sourceGaussianGreedyCopy_count_bound hLPos E 8192
    have hpSmall : (sourceGaussianCopyCount E L 8192 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 4) :=
      hpCount.trans hCopies
    obtain ⟨A, hAMeas, hAProb, hALower⟩ :=
      hNonflat E L (sourceGaussianCopyCount E L 8192) hm hSqrt hpPos hpSmall
    have hnR : (64 : ℝ) ≤ n := by exact_mod_cast hn
    have hpOneR : (1 : ℝ) ≤ sourceGaussianCopyCount E L 8192 := by exact_mod_cast hpPos
    have hPN : (1 / 64 : ℝ) < (sourceGaussianCopyCount E L 8192 : ℝ) * n := by nlinarith
    obtain ⟨B, hBMeas, hBProb, hBUpper⟩ := projectedGaussianCopies_uniform_coordinate_log_success
      (p := sourceGaussianCopyCount E L 8192) E (by norm_num : (0 : ℝ) < 1 / 64) hPN
    let F := {z | ((sourceGaussianFarCoordinates E L 8192 z).card : ℝ) <
      ((sourceGaussianExceptional E L 8192).card : ℝ) / 2}
    have hFProb : (63 / 64 : ℝ) ≤
        (standardGaussianCopiesLaw n (sourceGaussianCopyCount E L 8192)).real F :=
      (sourceGaussianGreedyCopy_success hnPos hLPos hLn E 8192 hJ).2
    have hAProb' : (63 / 64 : ℝ) ≤
        (standardGaussianCopiesLaw n (sourceGaussianCopyCount E L 8192)).real A := by
      have hFailure := gaussianNonflat_large_dimension_failure hL
      linarith
    have hBProb' : (63 / 64 : ℝ) ≤
        (standardGaussianCopiesLaw n (sourceGaussianCopyCount E L 8192)).real B := by
      linarith
    obtain ⟨z, hz⟩ := gaussian_three_success_sets_common_point
      (standardGaussianCopiesLaw n (sourceGaussianCopyCount E L 8192)) F A B
        hAMeas hBMeas hFProb hAProb' hBProb'
    exact sourceGaussian_exceptional_size_of_success_sample hn hL hLn hq hqSmall hLogRatio
      hRatioLarge E (by norm_num : (8192 : ℝ) ≤ 8192) hStructural z hz.1.1
        (hALower z hz.1.2) (hBUpper z hz.2)
  · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hJ
    simpa only [hEmpty, Finset.card_empty, Nat.cast_zero] using hCutoffNonneg

theorem gaussian_normal_dimension_of_codimension {n L : ℕ} (hLn : L ≤ n)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hE : Module.finrank ℂ E = n - L) :
    Module.finrank ℂ Eᗮ = L := by
  have hAdd := E.finrank_add_finrank_orthogonal
  have hAmbient : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n := by simp
  rw [hE, hAmbient] at hAdd
  omega

def FixedSubspaceGaussianAntiClusteringTheorem : Prop :=
  ∃ a₀ Cg : ℝ, 0 < a₀ ∧ 0 < Cg ∧
    ∀ C : ℝ, 1 ≤ C → ∀ σ : ℝ, 0 < σ → σ < 1 →
      ∀ a : ℝ, 0 < a → a ≤ a₀ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand C σ n d →
          ∀ L : ℕ, (n : ℝ) / (Real.log (n : ℝ)) ^ 288 ≤ L →
            (L : ℝ) ≤ (n : ℝ) / (d : ℝ) ^ 3 →
            ∀ E : Submodule ℂ (EuclideanSpace ℂ (Fin n)), Module.finrank ℂ E = n - L →
              FixedSubspaceStructural E L (sourceNormalRank a L) →
              1 - Cg * ((L : ℝ) / n) ≤
                (standardComplexGaussianVectorLaw n).real {z | GaussianAntiClusterEvent E L Cg z}

theorem fixed_subspace_gaussian_anti_clustering_theorem :
    FixedSubspaceGaussianAntiClusteringTheorem := by
  refine ⟨1 / 2048, 9216, by norm_num, by norm_num, ?_⟩
  intro C hC σ _ _ a ha haSmall
  have hSize := eventually_sourceGaussian_exceptional_size_uniform ha haSmall hC σ
  have hRanges := eventually_sourceGaussian_ranges_uniform ha haSmall hC σ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hSize.and hRanges)
  refine ⟨N, ?_⟩
  intro n hn d hBand L hLower hUpper E hE hStructural
  have hRange := (hN n hn).2 d hBand L hLower hUpper
  have hLn := hRange.2.2.1
  have hnPos : 0 < n := by have h := hRange.1; omega
  have hL : 2 ≤ L := by have h := hRange.2.1; omega
  have hNormal : L ≤ Module.finrank ℂ Eᗮ :=
    (gaussian_normal_dimension_of_codimension hLn E hE).symm.le
  have hExceptional := (hN n hn).1 d hBand L hLower hUpper E hNormal hStructural
  simpa only [show (8192 : ℝ) + 1024 = 9216 by norm_num] using
    sourceGaussian_anti_cluster_of_exceptional_bound hnPos hL hLn E
    (by norm_num : (0 : ℝ) ≤ 8192) hExceptional

end CircularLaw
