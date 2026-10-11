import CircularLaw.ExposureProcessDrift
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Filtration

/-!
# Completion drift at a wider integer barrier

The barrier (T-s)/8 fits the strict guarded insertion estimate, including
its integer boundary. A potential exp(2*a*h-a*(T-s)) gives the same
vanishing power of the conditional failure probability. This auxiliary
variant permits initial doubled height at most T/2.
-/

noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace CircularLaw

def wideBarrierExposureHeightPotential (a : ℝ) (T s h : ℕ) : ℝ :=
  Real.exp (2 * a * h - a * (T - s : ℕ))

theorem wide_barrier_height_potential_below_barrier {a : ℝ} (ha : 0 ≤ a)
    {T s h h' : ℕ} (hs : s < T) (hBelow : h < 2 * ((T - s) / 8))
    (hGrowth : h' ≤ h + 2) : wideBarrierExposureHeightPotential a T (s + 1) h' ≤ 1 := by
  have hNat : 2 * h' ≤ T - (s + 1) := by omega
  have hReal : 2 * (h' : ℝ) ≤ ((T - (s + 1) : ℕ) : ℝ) := by exact_mod_cast hNat
  apply Real.exp_le_one_iff.mpr
  nlinarith

theorem wide_barrier_height_potential_growth {a : ℝ} (ha : 0 ≤ a)
    {T s h h' : ℕ} (hs : s < T) (hGrowth : h' ≤ h + 2) :
    wideBarrierExposureHeightPotential a T (s + 1) h' ≤
      Real.exp (5 * a) * wideBarrierExposureHeightPotential a T s h := by
  have hTime : ((T - (s + 1) : ℕ) : ℝ) = ((T - s : ℕ) : ℝ) - 1 := by
    have hNat : T - s = T - (s + 1) + 1 := by omega
    have hCast : ((T - s : ℕ) : ℝ) = ((T - (s + 1) : ℕ) : ℝ) + 1 := by
      exact_mod_cast hNat
    linarith
  have hReal : (h' : ℝ) ≤ (h : ℝ) + 2 := by exact_mod_cast hGrowth
  rw [wideBarrierExposureHeightPotential, wideBarrierExposureHeightPotential, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hTime]
  nlinarith

theorem wide_barrier_height_potential_down {a : ℝ} (ha : 0 ≤ a)
    {T s h h' : ℕ} (hs : s < T) (hPos : 0 < h) (hDown : h' ≤ h - 1) :
    wideBarrierExposureHeightPotential a T (s + 1) h' ≤
      Real.exp (-1 * a) * wideBarrierExposureHeightPotential a T s h := by
  have hTime : ((T - (s + 1) : ℕ) : ℝ) = ((T - s : ℕ) : ℝ) - 1 := by
    have hNat : T - s = T - (s + 1) + 1 := by omega
    have hCast : ((T - s : ℕ) : ℝ) = ((T - (s + 1) : ℕ) : ℝ) + 1 := by
      exact_mod_cast hNat
    linarith
  have hReal : (h' : ℝ) ≤ (h : ℝ) - 1 := by
    exact_mod_cast (by omega : (h' : ℤ) ≤ (h : ℤ) - 1)
  rw [wideBarrierExposureHeightPotential, wideBarrierExposureHeightPotential, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hTime]
  nlinarith

theorem wide_barrier_exposure_terminal_exponential_bound
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ m0) (H : ℕ → Ω → ℕ) (T : ℕ)
    (hMeas : ∀ s, s ≤ T → Measurable[F s] (H s))
    (hInitial : ∀ x, (H 0 x : ℝ) ≤ (T : ℝ) / 2)
    (hGrowth : ∀ s, s < T → ∀ x, H (s + 1) x ≤ H s x + 2)
    {a : ℝ} (ha : Real.log 4 ≤ a)
    (hDrift : ∀ s, s < T → ∀ᵐ x ∂μ,
      2 * ((T - s) / 8) ≤ H s x →
      (μ[({y | H s y - 1 < H (s + 1) y}).indicator (fun _ => (1 : ℝ)) | F s]) x ≤
        Real.exp (-16 * a)) :
    μ.real {x | 0 < H T x} ≤ 2 * Real.exp (-2 * a) := by
  have haPos : 0 < a := lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 4)) ha
  have hHeight : ∀ s, s ≤ T → ∀ x, H s x ≤ 3 * T := by
    have hLocal : ∀ s, s ≤ T → ∀ x, H s x ≤ H 0 x + 2 * s := by
      intro s
      induction s with
      | zero => simp
      | succ s ih =>
        intro hs x
        have hOld := ih (by omega) x
        have hNew := hGrowth s (by omega) x
        omega
    intro s hs x
    have hInit : H 0 x ≤ T := by
      have := hInitial x
      exact_mod_cast (show (H 0 x : ℝ) ≤ T by linarith)
    have := hLocal s hs x
    omega
  let Z := fun s x => wideBarrierExposureHeightPotential a T s (H s x)
  have hZMeas : ∀ s, s ≤ T → StronglyMeasurable[F s] (Z s) := by
    intro s hs
    exact ((measurable_const.mul ((Measurable.of_discrete : Measurable (fun n : ℕ => (n : ℝ))).comp (hMeas s hs))).sub measurable_const).exp.stronglyMeasurable
  have hZNonneg : ∀ s x, 0 ≤ Z s x := fun _ _ => (Real.exp_pos _).le
  have hZInt : ∀ s, s ≤ T → Integrable (Z s) μ := by
    intro s hs
    apply (integrable_const (Real.exp (6 * a * T))).mono'
      ((hZMeas s hs).mono (F.le s)).aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hZNonneg s x)]
    apply Real.exp_le_exp.mpr
    have hBound : (H s x : ℝ) ≤ 3 * (T : ℝ) := by exact_mod_cast hHeight s hs x
    have hRemaining : (0 : ℝ) ≤ ((T - s : ℕ) : ℝ) := by positivity
    nlinarith
  have hCoeff : Real.exp (-1 * a) + Real.exp (-11 * a) ≤ 1 / 2 := by
    have hBase : Real.exp (-1 * a) ≤ 1 / 4 := by
      calc
        _ ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (by linarith)
        _ = 1 / 4 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    have hEleven : Real.exp (-11 * a) ≤ Real.exp (-1 * a) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hStep : ∀ s, s < T → (∫ x, Z (s + 1) x ∂μ) ≤
      1 + (Real.exp (-1 * a) + Real.exp (-11 * a)) * ∫ x, Z s x ∂μ := by
    intro s hs
    let A := {x | 2 * ((T - s) / 8) ≤ H s x}
    let B := {x | H s x - 1 < H (s + 1) x}
    have hA : MeasurableSet[F s] A := measurableSet_le measurable_const (hMeas s (by omega))
    have hB : MeasurableSet B := measurableSet_lt
      (((Measurable.of_discrete : Measurable (fun n : ℕ => n - 1)).comp ((hMeas s (by omega)).mono (F.le s) le_rfl)))
      ((hMeas (s + 1) (by omega)).mono (F.le (s + 1)) le_rfl)
    let w := A.indicator (Z s)
    have hWMeas : StronglyMeasurable[F s] w := (hZMeas s (by omega)).indicator hA
    have hWInt : Integrable w μ := (hZInt s (by omega)).indicator ((F.le s) _ hA)
    have hWNonneg : ∀ x, 0 ≤ w x := by
      intro x
      by_cases hx : x ∈ A <;> simp [w, hx, hZNonneg]
    have hWConditional : ∀ᵐ x ∂μ, w x = 0 ∨
        (μ[B.indicator (fun _ => (1 : ℝ)) | F s]) x ≤ Real.exp (-16 * a) := by
      filter_upwards [hDrift s hs] with x hx
      by_cases hxa : x ∈ A
      · exact Or.inr (hx hxa)
      · exact Or.inl (by simp [w, hxa])
    have hWeighted := weighted_indicator_integral_le_of_conditional_probability μ (F s)
      (F.le s) hB w hWMeas hWInt hWNonneg hWConditional
    have hWLe : (∫ x, w x ∂μ) ≤ ∫ x, Z s x ∂μ := by
      apply integral_mono hWInt (hZInt s (by omega))
      intro x
      by_cases hx : x ∈ A <;> simp [w, hx, hZNonneg]
    have hBadInt : Integrable (B.indicator w) μ := hWInt.indicator hB
    have hPoint : ∀ x, Z (s + 1) x ≤
        1 + Real.exp (-1 * a) * Z s x + Real.exp (5 * a) * B.indicator w x := by
      intro x
      by_cases hxa : x ∈ A
      · by_cases hxb : x ∈ B
        · have hg := wide_barrier_height_potential_growth haPos.le hs (hGrowth s hs x)
          simp only [Set.indicator_of_mem hxb, w, Set.indicator_of_mem hxa]
          change Z (s + 1) x ≤ 1 + Real.exp (-1 * a) * Z s x + Real.exp (5 * a) * Z s x
          have hPos : 0 ≤ Real.exp (-1 * a) * Z s x := mul_nonneg (Real.exp_pos _).le (hZNonneg s x)
          linarith
        · simp only [Set.indicator_of_notMem hxb, mul_zero, add_zero]
          have hDown : H (s + 1) x ≤ H s x - 1 := le_of_not_gt hxb
          by_cases hZero : H s x = 0
          · have hNew : H (s + 1) x = 0 := by omega
            have hSmall : Z (s + 1) x ≤ 1 := by
              apply Real.exp_le_one_iff.mpr
              simp only [hNew, Nat.cast_zero, mul_zero, zero_sub]
              have : (0 : ℝ) ≤ ((T - (s + 1) : ℕ) : ℝ) := by positivity
              nlinarith
            have : 0 ≤ Real.exp (-1 * a) * Z s x := mul_nonneg (Real.exp_pos _).le (hZNonneg s x)
            linarith
          · have hg := wide_barrier_height_potential_down haPos.le hs (Nat.pos_of_ne_zero hZero) hDown
            change Z (s + 1) x ≤ 1 + Real.exp (-1 * a) * Z s x
            linarith
      · have hBelow : H s x < 2 * ((T - s) / 8) := lt_of_not_ge hxa
        have hg := wide_barrier_height_potential_below_barrier haPos.le hs hBelow (hGrowth s hs x)
        have hPos : 0 ≤ Real.exp (-1 * a) * Z s x := mul_nonneg (Real.exp_pos _).le (hZNonneg s x)
        have hInd : B.indicator w x = 0 := by
          by_cases hxb : x ∈ B <;> simp [w, hxb, hxa]
        rw [hInd, mul_zero, add_zero]
        change Z (s + 1) x ≤ 1 + Real.exp (-1 * a) * Z s x
        linarith
    have hIntegral := integral_mono (hZInt (s + 1) (by omega))
      (((integrable_const 1).add ((hZInt s (by omega)).const_mul (Real.exp (-1 * a)))).add
        (hBadInt.const_mul (Real.exp (5 * a)))) hPoint
    change (∫ x, Z (s + 1) x ∂μ) ≤
      ∫ x, (1 + Real.exp (-1 * a) * Z s x) + Real.exp (5 * a) * B.indicator w x ∂μ at hIntegral
    have hSmallInt : Integrable (fun x => Real.exp (-1 * a) * Z s x) μ :=
      (hZInt s (by omega)).const_mul _
    have hFirstInt : Integrable (fun x => 1 + Real.exp (-1 * a) * Z s x) μ :=
      (integrable_const 1).add hSmallInt
    have hLastInt : Integrable (fun x => Real.exp (5 * a) * B.indicator w x) μ :=
      hBadInt.const_mul _
    rw [integral_add hFirstInt hLastInt, integral_add (integrable_const 1) hSmallInt,
      integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul, integral_const_mul] at hIntegral
    have hWeightedBound := hWeighted.trans (mul_le_mul_of_nonneg_left hWLe (Real.exp_pos _).le)
    have hFinalWeighted := mul_le_mul_of_nonneg_left hWeightedBound (Real.exp_pos (5 * a)).le
    have hExp : Real.exp (5 * a) * Real.exp (-16 * a) = Real.exp (-11 * a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← mul_assoc, hExp] at hFinalWeighted
    nlinarith
  have hMoment : ∀ s, s ≤ T → (∫ x, Z s x ∂μ) ≤ 2 := by
    intro s
    induction s with
    | zero =>
      intro _
      have hBound : ∀ x, Z 0 x ≤ 1 := by
        intro x
        apply Real.exp_le_one_iff.mpr
        simp only [Nat.sub_zero]
        have := hInitial x
        nlinarith
      have h := integral_mono (hZInt 0 (by omega)) (integrable_const 1) hBound
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h.trans (by simp : (∫ _ : Ω, (1 : ℝ) ∂μ) ≤ 2)
    | succ s ih =>
      intro hs
      have hOld := ih (by omega)
      have hNew := hStep s (by omega)
      have hNN : 0 ≤ ∫ x, Z s x ∂μ := integral_nonneg (hZNonneg s)
      nlinarith
  have hTail := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (hZNonneg T)) (hZInt T le_rfl) (Real.exp (2 * a))
  have hSubset : {x | 0 < H T x} ⊆ {x | Real.exp (2 * a) ≤ Z T x} := by
    intro x hx
    apply Real.exp_le_exp.mpr
    simp only [Nat.sub_self, Nat.cast_zero, mul_zero, sub_zero]
    have hOne : (1 : ℝ) ≤ H T x := by exact_mod_cast hx
    nlinarith
  have hMul := (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hSubset)
    (Real.exp_pos (2 * a)).le).trans (hTail.trans (hMoment T le_rfl))
  have hDiv : μ.real {x | 0 < H T x} ≤ 2 / Real.exp (2 * a) :=
    (le_div_iff₀ (Real.exp_pos (2 * a))).mpr (by simpa only [mul_comm] using hMul)
  simpa only [div_eq_mul_inv, ← Real.exp_neg, neg_mul] using hDiv

end CircularLaw
