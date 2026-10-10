import CircularLaw.UniformSumConcentration

/-!
# Concentration of a spread profile block

The two height branches in Section 3 are proved for the actual independent
uniform samples. Esseen covers heights at most 32; Miroshnikov and planar
packing cover larger heights. Above the inverse-weight reduction the
probability bound follows from one.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CircularLaw

def spreadBlockConstant : ℝ := 72 * miroshnikovConstant

theorem spreadBlockConstant_ge_one : 1 ≤ spreadBlockConstant := by
  unfold spreadBlockConstant
  linarith [miroshnikovConstant_ge_two]

theorem spreadBlockConstant_ge_esseen : 192 * (24 * Real.exp 1 / Real.pi) ≤
    spreadBlockConstant := by
  unfold spreadBlockConstant miroshnikovConstant miroshnikovStepConstant
  have h : 0 < 24 * Real.exp 1 / Real.pi := by positivity
  linarith

theorem spread_uniform_block_small_ball {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (Y : α → ℂ)
    {d k m : ℕ} {h τ : ℝ} (hd : 65536 ≤ d) (hk : 0 < k)
    (hm : 1 ≤ m) (hmd : m ≤ d) (hh : 2 ≤ h) (hτ : 1 ≤ τ)
    (hsep : ∀ a b, Y a ≠ Y b → (d : ℝ) / k ≤ dist (Y a) (Y b))
    (hatom : ∀ z, uniformProbability (fun a => Y a = z) ≤ 4 / (h + 3)) (z : ℂ) :
    uniformProbability (fun x : Fin m → α =>
      ‖(∑ a, Y (x a)) - z‖ ≤ τ * Real.sqrt (d : ℝ) / k) ≤
        spreadBlockConstant * τ ^ 2 * (h * Real.sqrt (m : ℝ))⁻¹ := by
  have hdPos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hkPos : (0 : ℝ) < k := by exact_mod_cast hk
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hRootPos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmPos
  have hhPos : 0 < h := by linarith
  have hτPos : 0 < τ := by linarith
  have hτSq : 1 ≤ τ ^ 2 := by nlinarith
  have hC : 0 ≤ spreadBlockConstant := by linarith [spreadBlockConstant_ge_one]
  let μ := (finiteUniformMeasure α).map Y
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map
    (measurable_of_finite Y).aemeasurable
  rw [uniform_sum_probability_eq]
  change (productSumLaw (fun _ : Fin m => μ)).real
    (Metric.closedBall z (τ * Real.sqrt (d : ℝ) / k)) ≤ _
  by_cases hSmall : τ ^ 2 ≤ h * Real.sqrt (m : ℝ)
  · by_cases hLow : h ≤ 32
    · have hAtoms : planarConcentration μ (Real.sqrt (d : ℝ) / k) ≤ 5 / 6 :=
        uniform_law_concentration_le Y _ _ (by norm_num)
          (spread_atom_le_five_sixths Y hd hk hh hsep hatom)
      have hRadius : Real.sqrt (d : ℝ) / k ≤ τ * Real.sqrt (d : ℝ) / k := by
        apply div_le_div_of_nonneg_right _ hkPos.le
        nlinarith [Real.sqrt_nonneg (d : ℝ)]
      have hRatio : (τ * Real.sqrt (d : ℝ) / k) / (Real.sqrt (d : ℝ) / k) = τ := by
        field_simp
      have hBound := five_sixths_deficit_product_sum_small_ball (fun _ : Fin m => μ)
        (by simpa using hm) (by positivity : 0 < Real.sqrt (d : ℝ) / k)
        hRadius (fun _ => hAtoms) z
      rw [hRatio, Fintype.card_fin] at hBound
      have hCE : 0 < 24 * Real.exp 1 / Real.pi := by positivity
      have hNum : (6 * (24 * Real.exp 1 / Real.pi)) * τ * h ≤ spreadBlockConstant * τ ^ 2 := by
        have h₁ := mul_le_mul_of_nonneg_left hLow
          (by positivity : 0 ≤ (6 * (24 * Real.exp 1 / Real.pi)) * τ)
        have h₂ := mul_le_mul spreadBlockConstant_ge_esseen
          (show τ ≤ τ ^ 2 by nlinarith) (by linarith : 0 ≤ τ) hC
        nlinarith
      apply hBound.trans
      calc
        _ = ((6 * (24 * Real.exp 1 / Real.pi)) * τ * h) /
            (h * Real.sqrt (m : ℝ)) := by field_simp
        _ ≤ spreadBlockConstant * τ ^ 2 / (h * Real.sqrt (m : ℝ)) :=
          div_le_div_of_nonneg_right hNum (by positivity)
        _ = _ := by rw [div_eq_mul_inv]
    · have hHigh : 32 < h := lt_of_not_ge hLow
      have hAtomWeak : ∀ w, uniformProbability (fun a => Y a = w) ≤ 4 / h := fun w =>
        (hatom w).trans (div_le_div_of_nonneg_left (by norm_num) hhPos (by linarith))
      have hRadiusEq : Real.sqrt 2 * (τ * Real.sqrt (d : ℝ) / k) =
          τ * Real.sqrt (2 * (d : ℝ)) / k := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      have hHalf : planarConcentration μ (Real.sqrt 2 * (τ * Real.sqrt (d : ℝ) / k)) ≤ 1 / 2 := by
        rw [hRadiusEq]
        exact uniform_law_concentration_le Y _ _ (by norm_num)
          (spread_atom_le_half Y hd hk hHigh hτPos.le hmd hSmall hsep hAtomWeak)
      have hAtomBound : planarConcentration μ (Real.sqrt 2 * (τ * Real.sqrt (d : ℝ) / k)) ≤
          (8 + 64 * τ ^ 2 / d) / h := by
        rw [hRadiusEq]
        exact uniform_law_concentration_le Y _ _ (by positivity)
          (spread_atom_source_scale Y (by omega) hk hhPos hτPos.le hsep hAtomWeak)
      have hCurrent : planarConcentration μ (τ * Real.sqrt (d : ℝ) / k) ≤ 1 / 2 := by
        apply (planarConcentration_mono μ ?_).trans hHalf
        have h := mul_le_mul_of_nonneg_right (Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2))
          (by positivity : 0 ≤ τ * Real.sqrt (d : ℝ) / k)
        simpa only [one_mul] using h
      have hBound := product_sum_miroshnikov_small_ball (fun _ : Fin m => μ)
        (by simpa using hm) (by positivity : 0 < τ * Real.sqrt (d : ℝ) / k)
        le_rfl (fun _ => hCurrent) (fun _ => hAtomBound) z
      rw [div_self (by positivity : τ * Real.sqrt (d : ℝ) / k ≠ 0),
        Fintype.card_fin, mul_one] at hBound
      have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      have hAtomScale : 8 + 64 * τ ^ 2 / d ≤ 72 * τ ^ 2 := by
        have h := div_le_self (by positivity : 0 ≤ 64 * τ ^ 2) hdOne
        nlinarith
      apply hBound.trans
      calc
        _ = miroshnikovConstant * (8 + 64 * τ ^ 2 / d) /
            (h * Real.sqrt (m : ℝ)) := by ring
        _ ≤ miroshnikovConstant * (72 * τ ^ 2) / (h * Real.sqrt (m : ℝ)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hAtomScale
            (by linarith [miroshnikovConstant_ge_two])) (by positivity)
        _ = _ := by unfold spreadBlockConstant; ring
  · have hLarge : h * Real.sqrt (m : ℝ) ≤ τ ^ 2 := (lt_of_not_ge hSmall).le
    have hOne : 1 ≤ spreadBlockConstant * τ ^ 2 * (h * Real.sqrt (m : ℝ))⁻¹ := by
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ (mul_pos hhPos hRootPos)).mpr
      have h := mul_le_mul_of_nonneg_right spreadBlockConstant_ge_one (sq_nonneg τ)
      nlinarith
    exact measureReal_le_one.trans hOne

end CircularLaw
