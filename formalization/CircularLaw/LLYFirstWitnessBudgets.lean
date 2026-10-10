import CircularLaw.LLYFirstWitnessProbability
import CircularLaw.AlmostConstantRanks

/-!
# First-steep witness budgets in the logarithmic degree regime

The existing floor rank supplies the exact sixteen-degree size budget.
For sufficiently large dimensions, a square-root stride and an explicit
logarithmic degree lower bound discharge the pair entropy condition.
-/

noncomputable section
open Classical Filter

namespace CircularLaw

theorem lly_first_rank_witness_budget {n d k : ℕ} (hd : 0 < d)
    (hk : k ≤ almostConstantRank n d) : 16 * d * k ≤ n := by
  have hkR : (k : ℝ) ≤ almostConstantRank n d := by exact_mod_cast hk
  have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * d)).mp
    (hkR.trans (almostConstantRank_upper hd))
  have hReal : (16 : ℝ) * d * k ≤ n := by nlinarith only [h]
  exact_mod_cast hReal

theorem lly_first_stride_entropy_budget {n d ℓ : ℕ} (hd : 0 < d)
    (hLog : 1 + Real.log 2 ≤ Real.log (n : ℝ))
    (hDegree : (16 / uniqueWitnessRate ^ 2) * Real.log (n : ℝ) ≤ d)
    (hStride : (ℓ : ℝ) ≤ Real.sqrt ((d : ℝ) / Real.log (n : ℝ))) :
    (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d := by
  have hRate := uniqueWitnessRate_pos
  have hLogTwo := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hLogPos : 0 < Real.log (n : ℝ) := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hDegreeScaled : 16 * Real.log (n : ℝ) ≤ uniqueWitnessRate ^ 2 * d := by
    have h := mul_le_mul_of_nonneg_right hDegree (sq_nonneg uniqueWitnessRate)
    have hCancel : (16 / uniqueWitnessRate ^ 2 * Real.log (n : ℝ)) * uniqueWitnessRate ^ 2 =
        16 * Real.log (n : ℝ) := by field_simp
    rw [hCancel] at h
    nlinarith only [h]
  have hRootSquare : (Real.sqrt ((d : ℝ) / Real.log (n : ℝ)) * Real.log (n : ℝ)) ^ 2 =
      (d : ℝ) * Real.log (n : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hdR.le hLogPos.le)]
    field_simp
  have hProduct := mul_le_mul_of_nonneg_right hDegreeScaled hdR.le
  have hRootBound : 2 * Real.sqrt ((d : ℝ) / Real.log (n : ℝ)) * Real.log (n : ℝ) ≤
      (uniqueWitnessRate / 2) * d := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    have hLeft : (2 * Real.sqrt ((d : ℝ) / Real.log (n : ℝ)) * Real.log (n : ℝ)) ^ 2 =
        4 * ((d : ℝ) * Real.log (n : ℝ)) := by
      calc
        _ = 4 * (Real.sqrt ((d : ℝ) / Real.log (n : ℝ)) * Real.log (n : ℝ)) ^ 2 := by ring
        _ = _ := by rw [hRootSquare]
    rw [hLeft]
    nlinarith only [hProduct]
  calc
    _ ≤ Real.sqrt ((d : ℝ) / Real.log (n : ℝ)) * (1 + Real.log n + Real.log 2) :=
      mul_le_mul_of_nonneg_right hStride (by linarith)
    _ ≤ Real.sqrt ((d : ℝ) / Real.log (n : ℝ)) * (2 * Real.log n) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt ((d : ℝ) / Real.log (n : ℝ)) * Real.log n := by ring
    _ ≤ _ := hRootBound

theorem eventually_lly_first_stride_entropy_budget :
    ∀ᶠ n : ℕ in atTop, ∀ d ℓ : ℕ, 0 < d →
      (16 / uniqueWitnessRate ^ 2) * Real.log (n : ℝ) ≤ d →
      (ℓ : ℝ) ≤ Real.sqrt ((d : ℝ) / Real.log (n : ℝ)) →
      (ℓ : ℝ) * (1 + Real.log n + Real.log 2) ≤ (uniqueWitnessRate / 2) * d := by
  have hLog : ∀ᶠ n : ℕ in atTop, 1 + Real.log 2 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually_ge_atTop _
  filter_upwards [hLog] with n hn
  intro d ℓ hd hDegree hStride
  exact lly_first_stride_entropy_budget hd hn hDegree hStride

theorem eventually_lly_first_witness_failure_polynomial (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d ℓ r k : ℕ, 0 < d → d ≤ n → 2 ≤ ℓ → 0 < k → k ≤ n →
      k ≤ almostConstantRank n d → ℓ ^ r < k →
      max (16 / uniqueWitnessRate ^ 2) ((2 / uniqueWitnessRate) * (A + 1)) * Real.log (n : ℝ) ≤ d →
      (ℓ : ℝ) ≤ Real.sqrt ((d : ℝ) / Real.log (n : ℝ)) →
      ∀ I : Finset (Fin n), (99 / 100 : ℝ) * n ≤ I.card →
        uniformProbability (fun rows : RowSliceMatrix n d => ¬LLYFirstWitness I ℓ r k rows) ≤
          (n : ℝ) ^ (-A) := by
  filter_upwards [eventually_lly_first_stride_entropy_budget, eventually_ge_atTop 3] with n hBudget hn
  intro d ℓ r k hd hdn hℓ hk hkn hFloor hRank hDegree hStride I hI
  have hLog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hEntropyDegree : (16 / uniqueWitnessRate ^ 2) * Real.log (n : ℝ) ≤ d :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hLog).trans hDegree
  have hFailureDegree : (2 / uniqueWitnessRate) * (A + 1) * Real.log (n : ℝ) ≤ d :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hLog).trans hDegree
  exact lly_first_witness_failure_polynomial hn hd hdn (by omega : 0 < ℓ) hk hkn I hI
    (lly_first_rank_witness_budget hd hFloor) (hBudget d ℓ hd hEntropyDegree hStride)
    (lly_first_scale_count hℓ hRank hkn) A hFailureDegree

end CircularLaw
