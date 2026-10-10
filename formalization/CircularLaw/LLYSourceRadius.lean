import CircularLaw.LLYThirdSourceProbability
import CircularLaw.LLYGradualRadiusBudgets

/-!
# A positive actual radius for both gradual and third steep adjoint branches

The radius is chosen from the proved norm constants. No sharp source
norm estimate is assumed. Both finite radius inequalities and the
resulting third-class probability estimate are checked here.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def llySourceAlmostRadius (n d : ℕ) (a₁ : ℝ) : ℝ :=
  min (Real.sqrt n / (5 * llyGradualNormConstant n d (llySourceScale n d a₁)
    (llySourceFirstRank n d a₁)))
    (llyThirdNetError d * Real.sqrt n / llyThirdSteepNormConstant n d (llySourceScale n d a₁))

theorem lly_third_norm_constant_pos {n d r : ℕ} (hn : 0 < n) (hd : 0 < d) :
    0 < llyThirdSteepNormConstant n d r :=
  (Real.sqrt_pos.mpr (by exact_mod_cast hn : (0 : ℝ) < n)).trans_le
    (lly_third_norm_constant_ge_sqrt hd)

theorem lly_source_almost_radius_pos {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (a₁ : ℝ) :
    0 < llySourceAlmostRadius n d a₁ := by
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hGradual := lly_gradual_norm_constant_pos (r := llySourceScale n d a₁)
    (k₁ := llySourceFirstRank n d a₁) hn hd
  have hThird := lly_third_norm_constant_pos (r := llySourceScale n d a₁) hn hd
  have hError : 0 < llyThirdNetError d := by
    unfold llyThirdNetError
    exact one_div_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hd) _)
  exact lt_min (div_pos hRoot (mul_pos (by norm_num) hGradual))
    (div_pos (mul_pos hError hRoot) hThird)

theorem lly_source_almost_radius_gradual (n d : ℕ) (a₁ : ℝ) :
    llySourceAlmostRadius n d a₁ ≤ Real.sqrt n /
      (5 * llyGradualNormConstant n d (llySourceScale n d a₁) (llySourceFirstRank n d a₁)) :=
  min_le_left _ _

theorem lly_source_almost_radius_third {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (a₁ : ℝ) :
    llyThirdSteepNormConstant n d (llySourceScale n d a₁) * llySourceAlmostRadius n d a₁ ≤
      llyThirdNetError d * Real.sqrt n := by
  have hThird := lly_third_norm_constant_pos (r := llySourceScale n d a₁) hn hd
  have hRadius := (le_div_iff₀ hThird).mp (min_le_right
    (Real.sqrt n / (5 * llyGradualNormConstant n d (llySourceScale n d a₁)
      (llySourceFirstRank n d a₁)))
    (llyThirdNetError d * Real.sqrt n / llyThirdSteepNormConstant n d (llySourceScale n d a₁)))
  change llySourceAlmostRadius n d a₁ * llyThirdSteepNormConstant n d (llySourceScale n d a₁) ≤
    llyThirdNetError d * Real.sqrt n at hRadius
  exact (mul_comm _ _).le.trans hRadius

theorem eventually_lly_third_source_radius_probability {C A a₁ a₂ a₃ α : ℝ}
    (hC : 1920000 ≤ C) (hA : 0 ≤ A) (hNormCost : A + 3 ≤ 9 * C)
    (ha₁ : 0 < a₁) (ha₁One : a₁ ≤ 1) (ha₂ : 0 < a₂)
    (ha₃ : 0 < a₃) (ha₃Small : a₃ ≤ 1 / 4096)
    (hFirstCost : 12288 * a₁ ≤ C * Real.log 2) (hα : α ≤ a₃ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log (n : ℝ) ≤ d → 2 * d ≤ n →
      ∀ ζ : ℂ, ‖ζ‖ ≤ Real.sqrt d * Real.log (Real.log (d : ℝ)) →
        uniformProbability (fun rows : RowSliceMatrix n d =>
          llyThirdAlmostUnitAdjointFailure ζ rows (llySourceStride n d)
            (llySourceScale n d a₁) (llySourceFirstRank n d a₁)
            (llySourceSecondRank n d a₂) (llySourceThirdRank n a₃) α (llySourceAlmostRadius n d a₁)
            ((llySourceAlmostRadius n d a₁ / Real.sqrt n) * llySourceAlmostRadius n d a₁ /
              Real.sqrt n)) ≤
                (n : ℝ) ^ (-A) + Real.exp (-(n : ℝ) * Real.log (d : ℝ) / 32) := by
  have hCPos : 0 < C := by linarith
  filter_upwards [eventually_ge_atTop 1,
    eventually_degree_property_uniform hCPos (eventually_ge_atTop 1),
    eventually_lly_third_source_adjoint_probability hC hA hNormCost ha₁ ha₁One ha₂ ha₃ ha₃Small
      hFirstCost hα] with n hn hDegrees hProbability
  intro d hLower hDegree ζ hShift
  have hd : 0 < d := by have h := hDegrees d hLower; omega
  exact hProbability d hLower hDegree (llySourceAlmostRadius n d a₁)
    (lly_source_almost_radius_pos hn hd a₁).le (lly_source_almost_radius_third hn hd a₁) ζ hShift

end CircularLaw
