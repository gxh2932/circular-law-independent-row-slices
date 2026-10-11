import CircularLaw.FourierPlancherel

/-!
# Fourier powers of bounded planar probability densities

The `L2` energy hypothesis is discharged from an actual probability
density bounded by one almost everywhere. Together with the superlevel
argument this proves the `C/q` estimate used in the source density bound.
The constant here is 200, rather than the source's numerical 47.
-/

noncomputable section
open MeasureTheory Real FourierTransform
open scoped FourierTransform ENNReal RealInnerProductSpace

namespace CircularLaw

structure UnitBoundedDensity (p : ℂ → ℝ) : Prop where
  integrable : Integrable p volume
  nonneg : ∀ᵐ x ∂volume, 0 ≤ p x
  le_one : ∀ᵐ x ∂volume, p x ≤ 1
  mass : (∫ x, p x) = 1

def densityLaw (p : ℂ → ℝ) : Measure ℂ :=
  volume.withDensity (fun x => ENNReal.ofReal (p x))

theorem densityLaw_probability {p : ℂ → ℝ} (hp : UnitBoundedDensity p) :
    IsProbabilityMeasure (densityLaw p) := by
  constructor
  rw [densityLaw, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hp.integrable hp.nonneg, hp.mass]
  simp

theorem unit_bounded_density_sq {p : ℂ → ℝ} (hp : UnitBoundedDensity p) :
    Integrable (fun x => p x ^ 2) volume := by
  apply hp.integrable.mono'
    (hp.integrable.aestronglyMeasurable.aemeasurable.pow_const (2 : ℕ)).aestronglyMeasurable
  filter_upwards [hp.nonneg, hp.le_one] with x hx hy
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith

theorem unit_bounded_density_complex_memLp {p : ℂ → ℝ} (hp : UnitBoundedDensity p) :
    MemLp (fun x => (p x : ℂ)) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm hp.integrable.ofReal.aestronglyMeasurable).mpr
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using unit_bounded_density_sq hp

theorem densityLaw_charFun_fourier {p : ℂ → ℝ} (hp : UnitBoundedDensity p) (t : ℂ) :
    charFun (densityLaw p) ((-(2 * Real.pi)) • t) = 𝓕 (fun x => (p x : ℂ)) t := by
  rw [charFun_apply, densityLaw, integral_withDensity_eq_integral_toReal_smul₀
    hp.integrable.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [hp.nonneg] with x hx
  rw [ENNReal.toReal_ofReal hx, real_inner_smul_right, Complex.real_smul, smul_eq_mul,
    show -(2 * Real.pi) = -2 * Real.pi by ring, mul_comm]

theorem bounded_density_energy_integrable {p : ℂ → ℝ} (hp : UnitBoundedDensity p) :
    Integrable (fourierEnergy (densityLaw p)) volume := by
  have h := (pointwise_fourier_memLp (f := fun x => (p x : ℂ)) hp.integrable.ofReal
    (unit_bounded_density_complex_memLp hp)).norm.integrable_sq
  change Integrable (fun t => ‖charFun (densityLaw p) ((-(2 * Real.pi)) • t)‖ ^ 2) volume
  simpa only [densityLaw_charFun_fourier hp] using h

theorem bounded_density_energy_bound {p : ℂ → ℝ} (hp : UnitBoundedDensity p) :
    (∫ t, fourierEnergy (densityLaw p) t) ≤ 1 := by
  simp only [fourierEnergy, densityLaw_charFun_fourier hp]
  rw [pointwise_plancherel (f := fun x => (p x : ℂ)) hp.integrable.ofReal
    (unit_bounded_density_complex_memLp hp)]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← hp.mass]
  apply integral_mono_ae (unit_bounded_density_sq hp) hp.integrable
  filter_upwards [hp.nonneg, hp.le_one] with x hx hy
  nlinarith

/-- The Fourier-power dependency follows from the bounded-density
hypotheses, with no Plancherel or energy estimate left as an assumption. -/
theorem bounded_density_fourier_power {p : ℂ → ℝ} (hp : UnitBoundedDensity p)
    {q : ℝ} (hq : 2 ≤ q) :
    (∫ t, Real.rpow ‖𝓕 (fun x => (p x : ℂ)) t‖ q) ≤ 200 / q := by
  haveI : IsProbabilityMeasure (densityLaw p) := densityLaw_probability hp
  have h := fourier_power_of_energy_bound (densityLaw p)
    (bounded_density_energy_integrable hp) (bounded_density_energy_bound hp) hq
  simpa only [densityLaw_charFun_fourier hp] using h

theorem bounded_density_fourier_power_integrable {p : ℂ → ℝ} (hp : UnitBoundedDensity p)
    {q : ℝ} (hq : 2 ≤ q) :
    Integrable (fun t => Real.rpow ‖𝓕 (fun x => (p x : ℂ)) t‖ q) volume := by
  haveI : IsProbabilityMeasure (densityLaw p) := densityLaw_probability hp
  have h := fourier_norm_rpow_integrable (densityLaw p)
    (bounded_density_energy_integrable hp) hq
  simpa only [densityLaw_charFun_fourier hp] using h

def BoundedDensityFourierPowerLemma : Prop :=
  ∀ (p : ℂ → ℝ), UnitBoundedDensity p → ∀ (q : ℝ), 2 ≤ q →
    (∫ t, Real.rpow ‖𝓕 (fun x => (p x : ℂ)) t‖ q) ≤ 200 / q

theorem bounded_density_fourier_power_lemma : BoundedDensityFourierPowerLemma := by
  intro p hp q hq
  exact bounded_density_fourier_power hp hq

end CircularLaw
