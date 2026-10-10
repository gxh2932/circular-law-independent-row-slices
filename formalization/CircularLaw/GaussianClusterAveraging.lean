import CircularLaw.ClusterPairCounting

/-!
# Gaussian anti-clustering after the large correlation clusters are removed

For the actual projected Gaussian vector, a retained set with at most `b`
strongly correlated neighbours per index has the source disk-count failure
bound. The bound uses neither independence between projected coordinates
nor an assumed small-ball estimate.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

def gaussianClusterRadius (α β s : ℝ) : ℝ :=
  α * s / (4 * Real.sqrt (Real.log (1 / β)))

theorem gaussianClusterRadius_eq_source (α β s : ℝ) :
    gaussianClusterRadius α β s = α * s / Real.sqrt (16 * Real.log (1 / β)) := by
  rw [gaussianClusterRadius, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  norm_num

theorem gaussianClusterRadius_twice (α β s : ℝ) :
    2 * gaussianClusterRadius α β s = (α * (s / 2)) / Real.sqrt (Real.log (1 / β)) := by
  unfold gaussianClusterRadius
  ring

theorem projectedGaussian_bounded_correlation_anti_cluster {n b : ℕ} (hb : 0 < b)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (K : Finset (Fin n))
    {α β s : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (hs : 0 ≤ s)
    (hCorr : ∀ i ∈ K, (K.filter (projectedGaussianStronglyCorrelated E α β i)).card ≤ b) :
    (standardComplexGaussianVectorLaw n).real
      {z | ∃ w : ℂ, 2 * b ≤
        (K.filter (fun j => ‖projectedComplexGaussian E z j - w‖ ≤
          gaussianClusterRadius α β s)).card} ≤ (s * (n : ℝ)) ^ 2 / (2 * (b : ℝ) ^ 2) := by
  have hY (i : Fin n) : Measurable (fun z => projectedComplexGaussian E z i) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) i).comp
      (projectedComplexGaussian_continuous E)).measurable
  have hSmall : ∀ i ∈ K, ∀ j ∈ K, ¬ projectedGaussianStronglyCorrelated E α β i j →
      (standardComplexGaussianVectorLaw n).real
        {z | ‖projectedComplexGaussian E z i - projectedComplexGaussian E z j‖ ≤
          2 * gaussianClusterRadius α β s} ≤ s ^ 2 := by
    intro i _ j _ hNot
    have h := projectedGaussian_noncorrelation_smallBall E i j hα hβ hβ1
      (div_nonneg hs (by norm_num : (0 : ℝ) ≤ 2)) hNot 0
    rw [← gaussianClusterRadius_twice] at h
    simp only [sub_zero] at h
    apply h.trans
    nlinarith only [sq_nonneg s]
  have h := bounded_correlation_large_disk_probability (standardComplexGaussianVectorLaw n) hb
    K (projectedGaussianStronglyCorrelated E α β) (fun z j => projectedComplexGaussian E z j)
    (gaussianClusterRadius α β s) hY hCorr hSmall
  apply h.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hCard : (K.card : ℝ) ≤ (n : ℝ) := by
    have hNat : K.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ K
    exact_mod_cast hNat
  exact pow_le_pow_left₀ (mul_nonneg hs (Nat.cast_nonneg _))
    (mul_le_mul_of_nonneg_left hCard hs) 2

end CircularLaw
