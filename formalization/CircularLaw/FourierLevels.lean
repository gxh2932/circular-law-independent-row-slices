import CircularLaw.CharacteristicDefect
import CircularLaw.Tensorization
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Planar Fourier superlevel sets

The dilation estimate controls the area of the sets where a characteristic
function is close to one. The energy bound is an explicit hypothesis here;
It is derived from a bounded probability density in `BoundedDensity.lean`.
The frequency normalization is the source's `exp(-2*pi*i*inner(t,x))`,
so its Plancherel bound has no additional dimensional constant.
-/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace Pointwise ENNReal

namespace CircularLaw

theorem integrable_superlevel_measure_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {f : Ω → ℝ} (hf : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 < a) :
    μ {x | a ≤ f x} ≤ ENNReal.ofReal ((∫ x, f x ∂μ) / a) := by
  have h := (hf.const_mul (1 / a)).measure_le_integral
    (ae_of_all _ fun x => mul_nonneg (by positivity) (hf0 x))
    (s := {x | a ≤ f x}) (by
      intro x hx
      rw [one_div, ← div_eq_inv_mul]
      exact (le_div_iff₀ ha).mpr (by simpa using hx))
  rw [integral_const_mul] at h
  simpa only [one_div, ← div_eq_inv_mul] using h

theorem integrable_superlevel_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {f : Ω → ℝ} (hf : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 < a) :
    μ {x | a ≤ f x} ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (integrable_superlevel_measure_le μ hf hf0 ha)

theorem integrable_superlevel_area_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {f : Ω → ℝ} (hf : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 < a) :
    μ.real {x | a ≤ f x} ≤ (∫ x, f x ∂μ) / a := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (integrable_superlevel_measure_le μ hf hf0 ha)
  simpa only [measureReal_def,
    ENNReal.toReal_ofReal (div_nonneg (integral_nonneg hf0) ha.le)] using h

theorem floor_reciprocal_lower {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    1 / 4 ≤ (⌊1 / (2 * δ)⌋₊ : ℝ) * δ := by
  have hone : 1 ≤ ⌊1 / (2 * δ)⌋₊ := (Nat.one_le_floor_iff _).mpr
    ((le_div_iff₀ (by positivity : 0 < 2 * δ)).mpr (by linarith))
  have hone' : (1 : ℝ) ≤ ⌊1 / (2 * δ)⌋₊ := by exact_mod_cast hone
  have hlt := Nat.lt_floor_add_one (1 / (2 * δ))
  have h := (div_lt_iff₀ (by positivity : 0 < 2 * δ)).mp hlt
  nlinarith

def fourierEnergy (μ : Measure ℂ) (t : ℂ) : ℝ :=
  ‖charFun μ ((-(2 * Real.pi)) • t)‖ ^ 2

def fourierSuperlevel (μ : Measure ℂ) (δ : ℝ) : Set ℂ :=
  {t | 1 - δ ^ 2 ≤ fourierEnergy μ t}

theorem fourierEnergy_measurable (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    Measurable (fourierEnergy μ) :=
  ((measurable_charFun (μ := μ)).comp (measurable_const_smul _)).norm.pow_const 2

theorem fourierSuperlevel_measurable (μ : Measure ℂ) [IsProbabilityMeasure μ] (δ : ℝ) :
    MeasurableSet (fourierSuperlevel μ δ) :=
  measurableSet_le measurable_const (fourierEnergy_measurable μ)

theorem fourierSuperlevel_dilate_subset (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) :
    (⌊1 / (2 * δ)⌋₊ : ℝ) • fourierSuperlevel μ δ ⊆ fourierSuperlevel μ (1 / 2) := by
  rintro t ⟨s, hs, rfl⟩
  have h := charFun_superlevel_dilate μ hδ hs
  norm_num only [fourierSuperlevel, Set.mem_setOf_eq, fourierEnergy] at h ⊢
  simpa only [smul_smul, mul_comm] using h

theorem fourierSuperlevel_half_finite (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hint : Integrable (fourierEnergy μ) volume) :
    volume (fourierSuperlevel μ (1 / 2)) ≠ ∞ := by
  convert integrable_superlevel_finite volume hint (fun _ => sq_nonneg _) (by norm_num :
    (0 : ℝ) < 3 / 4) using 1; norm_num [fourierSuperlevel]

theorem fourierSuperlevel_half_area (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hint : Integrable (fourierEnergy μ) volume)
    (henergy : (∫ t, fourierEnergy μ t) ≤ 1) :
    volume.real (fourierSuperlevel μ (1 / 2)) ≤ 4 / 3 := by
  have h := integrable_superlevel_area_le volume hint (fun _ => sq_nonneg _)
    (by norm_num : (0 : ℝ) < 3 / 4)
  norm_num [fourierSuperlevel] at h ⊢
  linarith

/-- Integer dilation and the planar area scaling give the source's
`64 * delta^2 / 3` superlevel bound. -/
theorem fourierSuperlevel_area (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hint : Integrable (fourierEnergy μ) volume)
    (henergy : (∫ t, fourierEnergy μ t) ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    volume.real (fourierSuperlevel μ δ) ≤ (64 / 3) * δ ^ 2 := by
  let k : ℝ := ⌊1 / (2 * δ)⌋₊
  have hkd : 1 / 4 ≤ k * δ := floor_reciprocal_lower hδ hδhalf
  have hk : 0 < k := by nlinarith
  have hmono := measure_mono (μ := volume) (fourierSuperlevel_dilate_subset μ hδ)
  have hfinite := ne_top_of_le_ne_top (fourierSuperlevel_half_finite μ hint) hmono
  have hscale : volume (k • fourierSuperlevel μ δ) =
      ENNReal.ofReal (k ^ 2) * volume (fourierSuperlevel μ δ) := by
    rw [Measure.addHaar_smul_of_nonneg volume hk.le, Complex.finrank_real_complex]
  have hAfin : volume (fourierSuperlevel μ δ) ≠ ∞ := by
    rw [hscale] at hfinite
    exact (ENNReal.lt_top_of_mul_ne_top_right hfinite
      (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hk))).ne
  have hm := measureReal_mono (fourierSuperlevel_dilate_subset μ hδ)
    (fourierSuperlevel_half_finite μ hint)
  have hrscale : volume.real (k • fourierSuperlevel μ δ) =
      k ^ 2 * volume.real (fourierSuperlevel μ δ) := by
    rw [measureReal_def, hscale, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg k), measureReal_def]
  rw [hrscale] at hm
  have harea := hm.trans (fourierSuperlevel_half_area μ hint henergy)
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hkd 2
  have hnonneg : 0 ≤ volume.real (fourierSuperlevel μ δ) := measureReal_nonneg
  have hmult := mul_le_mul_of_nonneg_right harea (sq_nonneg δ)
  nlinarith [mul_le_mul_of_nonneg_right hsq hnonneg]

theorem fourierEnergy_le_one (μ : Measure ℂ) [IsProbabilityMeasure μ] (t : ℂ) :
    fourierEnergy μ t ≤ 1 := by
  simpa only [fourierEnergy, one_pow] using
    pow_le_pow_left₀ (norm_nonneg _)
      (norm_charFun_le_one (μ := μ) ((-(2 * Real.pi)) • t)) 2

theorem rpow_le_exp_neg_defect {x r : ℝ} (hx : 0 ≤ x) (hr : 0 < r) :
    Real.rpow x r ≤ Real.exp (-(r * (1 - x))) := by
  simp only [Real.rpow_eq_pow]
  rcases hx.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow hr.ne']
    exact (Real.exp_pos _).le
  · rw [Real.rpow_def_of_pos h]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos h) hr.le
    nlinarith

theorem rpow_le_cutoff_mul {x a r : ℝ} (hx : 0 ≤ x) (hxa : x ≤ a) (hr : 1 ≤ r) :
    Real.rpow x r ≤ Real.rpow a (r - 1) * x := by
  have heq : Real.rpow x r = Real.rpow x (r - 1) * x := by
    have h := Real.rpow_add_of_nonneg hx (sub_nonneg.mpr hr) (show (0 : ℝ) ≤ 1 by norm_num)
    simpa only [sub_add_cancel, Real.rpow_one] using h
  rw [heq]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx hxa (sub_nonneg.mpr hr)) hx

theorem cutoff_power_decay {r : ℝ} (hr : 1 ≤ r) :
    Real.rpow (3 / 4) (r - 1) ≤ 12 / r := by
  simp only [Real.rpow_eq_pow]
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hexp : Real.exp (-(r / 4)) ≤ 4 / r := by
    rw [Real.exp_neg]
    apply (le_div_iff₀ hr0).mpr
    apply (inv_mul_le_iff₀ (Real.exp_pos _)).mpr
    linarith [Real.add_one_le_exp (r / 4)]
  calc
    _ ≤ Real.exp (-(r - 1) / 4) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right
        (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 4))
        (sub_nonneg.mpr hr)
      nlinarith
    _ = Real.exp (1 / 4) * Real.exp (-(r / 4)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ 3 * (4 / r) := by
      apply mul_le_mul
      · exact (Real.exp_le_exp.mpr (by norm_num : (1 / 4 : ℝ) ≤ 1)).trans
          Real.exp_one_lt_three.le
      · exact hexp
      · exact (Real.exp_pos _).le
      · norm_num
    _ = 12 / r := by ring

/-- The area bound becomes a linear sublevel estimate for the defect.
The large-sublevel case uses only the finite area of the high-energy set. -/
theorem fourier_defect_sublevel (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hint : Integrable (fourierEnergy μ) volume)
    (henergy : (∫ t, fourierEnergy μ t) ≤ 1) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (volume.restrict (fourierSuperlevel μ (1 / 2))).real
      {t | r * (1 - fourierEnergy μ t) < (n : ℝ) + 1} ≤
      (64 / (3 * r)) * ((n : ℝ) + 1) := by
  let a : ℝ := ((n : ℝ) + 1) / r
  have ha : 0 < a := by dsimp [a]; positivity
  have hδ : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hB : MeasurableSet {t | r * (1 - fourierEnergy μ t) < (n : ℝ) + 1} := by
    apply measurableSet_lt _ measurable_const
    exact measurable_const.mul (measurable_const.sub (fourierEnergy_measurable μ))
  rw [measureReal_restrict_apply hB]
  by_cases hsmall : a ≤ 1 / 4
  · have hhalf : Real.sqrt a ≤ 1 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num,
      by norm_num at hsmall ⊢; exact hsmall⟩
    have hsubset : {t | r * (1 - fourierEnergy μ t) < (n : ℝ) + 1} ∩
        fourierSuperlevel μ (1 / 2) ⊆ fourierSuperlevel μ (Real.sqrt a) := by
      intro t ht
      change 1 - Real.sqrt a ^ 2 ≤ fourierEnergy μ t
      rw [hsq]
      have h : 1 - fourierEnergy μ t < a :=
        (lt_div_iff₀ hr).mpr (by simpa only [mul_comm] using ht.1)
      linarith
    have hfinite : volume (fourierSuperlevel μ (Real.sqrt a)) ≠ ∞ := by
      have h := integrable_superlevel_finite volume hint (fun _ => sq_nonneg _)
        (a := 1 - a) (by linarith)
      simpa only [fourierSuperlevel, hsq] using h
    calc
      _ ≤ volume.real (fourierSuperlevel μ (Real.sqrt a)) := measureReal_mono hsubset hfinite
      _ ≤ (64 / 3) * Real.sqrt a ^ 2 := fourierSuperlevel_area μ hint henergy hδ hhalf
      _ = _ := by rw [hsq]; dsimp [a]; ring
  · have h : volume.real ({t | r * (1 - fourierEnergy μ t) < (n : ℝ) + 1} ∩
        fourierSuperlevel μ (1 / 2)) ≤ volume.real (fourierSuperlevel μ (1 / 2)) :=
      measureReal_mono Set.inter_subset_right (fourierSuperlevel_half_finite μ hint)
    have hlarge : 1 / 4 < a := lt_of_not_ge hsmall
    have hc : 4 / 3 ≤ (64 / (3 * r)) * ((n : ℝ) + 1) := by
      have heq : (64 / (3 * r)) * ((n : ℝ) + 1) = (64 / 3) * a := by
        dsimp [a]; ring
      rw [heq]
      linarith
    exact h.trans ((fourierSuperlevel_half_area μ hint henergy).trans hc)

theorem fourier_high_energy_laplace (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hint : Integrable (fourierEnergy μ) volume)
    (henergy : (∫ t, fourierEnergy μ t) ≤ 1) {r : ℝ} (hr : 0 < r) :
    (∫ t in fourierSuperlevel μ (1 / 2), Real.exp (-(r * (1 - fourierEnergy μ t)))) ≤
      (256 / 3) / r := by
  haveI : IsFiniteMeasure (volume.restrict (fourierSuperlevel μ (1 / 2))) :=
    isFiniteMeasure_restrict.mpr (fourierSuperlevel_half_finite μ hint)
  have h := integral_exp_neg_le_of_sublevel_bound
    (volume.restrict (fourierSuperlevel μ (1 / 2)))
    (measurable_const.mul (measurable_const.sub (fourierEnergy_measurable μ)))
    (fun t => mul_nonneg hr.le (sub_nonneg.mpr (fourierEnergy_le_one μ t)))
    (fourier_defect_sublevel μ hint henergy hr)
  convert h using 1
  ring

theorem fourierEnergy_power_integrable (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hint : Integrable (fourierEnergy μ) volume) {r : ℝ} (hr : 1 ≤ r) :
    Integrable (fun t => Real.rpow (fourierEnergy μ t) r) volume := by
  simp only [Real.rpow_eq_pow]
  apply hint.mono' ((fourierEnergy_measurable μ).pow_const r).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_of_nonneg (Real.rpow_nonneg
    (show 0 ≤ fourierEnergy μ t from sq_nonneg _) _)]
  exact Real.rpow_le_self_of_le_one (sq_nonneg _) (fourierEnergy_le_one μ t) hr

/-- The high-energy part decays by the area estimate; the remaining part
decays exponentially. This version uses a looser absolute constant than
LLTTY19 Lemma 2.6, sufficient for its downstream density estimate. -/
theorem fourierEnergy_power_bound (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hint : Integrable (fourierEnergy μ) volume)
    (henergy : (∫ t, fourierEnergy μ t) ≤ 1) {r : ℝ} (hr : 1 ≤ r) :
    (∫ t, Real.rpow (fourierEnergy μ t) r) ≤ 100 / r := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let A := fourierSuperlevel μ (1 / 2)
  have hA : MeasurableSet A := fourierSuperlevel_measurable μ _
  have hFp := fourierEnergy_power_integrable μ hint hr
  haveI : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.mpr (fourierSuperlevel_half_finite μ hint)
  have hexp : Integrable (fun t => Real.exp (-(r * (1 - fourierEnergy μ t))))
      (volume.restrict A) := by
    apply integrable_of_abs_bound _
      ((measurable_const.mul (measurable_const.sub (fourierEnergy_measurable μ))).neg.exp)
      (C := 1)
    intro t
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg hr0.le (sub_nonneg.mpr (fourierEnergy_le_one μ t)))
  have hhigh : (∫ t in A, Real.rpow (fourierEnergy μ t) r) ≤ (256 / 3) / r := by
    exact (integral_mono (hFp.mono_measure volume.restrict_le_self) hexp
      (fun t => rpow_le_exp_neg_defect (sq_nonneg _) hr0)).trans
      (fourier_high_energy_laplace μ hint henergy hr0)
  let c := Real.rpow (3 / 4) (r - 1)
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hlow : (∫ t in Aᶜ, Real.rpow (fourierEnergy μ t) r) ≤ 12 / r := by
    calc
      _ ≤ ∫ t in Aᶜ, c * fourierEnergy μ t := by
        apply integral_mono_ae (hFp.mono_measure volume.restrict_le_self)
          ((hint.const_mul c).mono_measure volume.restrict_le_self)
        filter_upwards [ae_restrict_mem hA.compl] with t ht
        have ht' : fourierEnergy μ t ≤ 3 / 4 := by
          change ¬1 - (1 / 2 : ℝ) ^ 2 ≤ fourierEnergy μ t at ht
          norm_num at ht
          linarith
        exact rpow_le_cutoff_mul (sq_nonneg _) ht' hr
      _ = c * ∫ t in Aᶜ, fourierEnergy μ t := integral_const_mul _ _
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left
        ((integral_mono_measure volume.restrict_le_self
          (ae_of_all _ fun _ => sq_nonneg _) hint).trans henergy) hc
      _ = c := mul_one _
      _ ≤ 12 / r := cutoff_power_decay hr
  rw [← integral_add_compl hA hFp]
  have h := add_le_add hhigh hlow
  exact h.trans (by rw [← add_div]; apply (div_le_div_iff_of_pos_right hr0).mpr; norm_num)

theorem fourier_norm_rpow_eq_energy (μ : Measure ℂ) (q : ℝ) (t : ℂ) :
    Real.rpow ‖charFun μ ((-(2 * Real.pi)) • t)‖ q =
      Real.rpow (fourierEnergy μ t) (q / 2) := by
  simp only [Real.rpow_eq_pow, fourierEnergy]
  rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring

theorem fourier_norm_rpow_integrable (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hint : Integrable (fourierEnergy μ) volume) {q : ℝ} (hq : 2 ≤ q) :
    Integrable (fun t => Real.rpow ‖charFun μ ((-(2 * Real.pi)) • t)‖ q) volume := by
  simp_rw [fourier_norm_rpow_eq_energy]
  exact fourierEnergy_power_integrable μ hint (by linarith)

theorem fourier_power_of_energy_bound (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hint : Integrable (fourierEnergy μ) volume)
    (henergy : (∫ t, fourierEnergy μ t) ≤ 1) {q : ℝ} (hq : 2 ≤ q) :
    (∫ t, Real.rpow ‖charFun μ ((-(2 * Real.pi)) • t)‖ q) ≤ 200 / q := by
  simp_rw [fourier_norm_rpow_eq_energy]
  have h := fourierEnergy_power_bound μ hint henergy (r := q / 2) (by linarith)
  convert h using 1
  field_simp
  norm_num

end CircularLaw
