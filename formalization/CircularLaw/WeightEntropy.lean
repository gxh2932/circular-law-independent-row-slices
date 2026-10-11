import CircularLaw.CountableEntropy
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Entropy of integer-valued laws

The named manuscript lemma holds for every integer-valued law. Infinite
dispersion is treated in the extended reals; finite dispersion implies
finite entropy. Averaging the reference-law comparison over an independent
center gives the expected pair distance directly, without needing a median.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace CircularLaw

/-- The natural logarithm of `1+D`, extended by infinity at infinite `D`. -/
def extendedLogOnePlus (D : ℝ≥0∞) : ℝ≥0∞ :=
  if D = ∞ then ∞ else ENNReal.ofReal (Real.log (1 + D.toReal))

def weightEntropyConstant : ℝ := 2 + Real.log 4

theorem weightEntropyConstant_pos : 0 < weightEntropyConstant := by
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  dsimp [weightEntropyConstant]
  linarith

theorem integer_entropy_dispersion_finite (p : PMF ℤ) (hD : integerDispersion p ≠ ∞) :
    integerEntropy p ≤ ENNReal.ofReal
      (weightEntropyConstant + Real.log (1 + (integerDispersion p).toReal)) := by
  let t := (integerDispersion p).toReal
  let α := 1 / (1 + t)
  have ht : 0 ≤ t := ENNReal.toReal_nonneg
  have htPos : 0 < 1 + t := by linarith
  have hα : 0 < α := one_div_pos.mpr htPos
  have hαOne : α ≤ 1 := (div_le_one htPos).mpr (by linarith)
  have hαMoment : α * t ≤ 1 := by
    dsimp [α]
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    exact (div_le_one htPos).mpr (by linarith)
  have hRatio : 4 / α = 4 * (1 + t) := by
    dsimp [α]
    field_simp
  have hLog : Real.log (4 / α) = Real.log 4 + Real.log (1 + t) := by
    rw [hRatio, Real.log_mul (by norm_num) htPos.ne']
  have hLogNonneg : 0 ≤ Real.log (4 / α) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hα).mpr (by linarith)
  have hBase : 0 ≤ 1 + Real.log (4 / α) := by linarith
  have hBound := integer_entropy_gibbs_bound hα hαOne p
  rw [← ENNReal.ofReal_toReal hD] at hBound
  change integerEntropy p ≤ ENNReal.ofReal (1 + Real.log (4 / α)) +
    ENNReal.ofReal α * ENNReal.ofReal t at hBound
  rw [← ENNReal.ofReal_mul hα.le, ← ENNReal.ofReal_add hBase (mul_nonneg hα.le ht)] at hBound
  exact hBound.trans (ENNReal.ofReal_le_ofReal (by
    change 1 + Real.log (4 / α) + α * t ≤ weightEntropyConstant + Real.log (1 + t)
    rw [hLog]
    dsimp [weightEntropyConstant]
    linarith))

theorem integer_entropy_dispersion (p : PMF ℤ) :
    integerEntropy p ≤ ENNReal.ofReal weightEntropyConstant +
      extendedLogOnePlus (integerDispersion p) := by
  by_cases hD : integerDispersion p = ∞
  · simp only [extendedLogOnePlus, hD, if_true, add_top]
    exact le_top
  · have hLog : 0 ≤ Real.log (1 + (integerDispersion p).toReal) :=
      Real.log_nonneg (by linarith [ENNReal.toReal_nonneg (a := integerDispersion p)])
    simpa only [extendedLogOnePlus, if_neg hD,
      ENNReal.ofReal_add weightEntropyConstant_pos.le hLog] using
      integer_entropy_dispersion_finite p hD

theorem integer_entropy_ne_top (p : PMF ℤ) (hD : integerDispersion p ≠ ∞) :
    integerEntropy p ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (integer_entropy_dispersion_finite p hD)

theorem integerEntropy_eq_ofReal_tsum (p : PMF ℤ) (hD : integerDispersion p ≠ ∞) :
    integerEntropy p = ENNReal.ofReal (∑' j : ℤ, integerEntropyAtom p j) := by
  have hfinite : (∑' j : ℤ, ENNReal.ofReal (integerEntropyAtom p j)) ≠ ∞ :=
    integer_entropy_ne_top p hD
  have hreal : (integerEntropy p).toReal = ∑' j : ℤ, integerEntropyAtom p j := by
    rw [integerEntropy, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (integerEntropyAtom_nonneg p _)]
  rw [← hreal]
  exact (ENNReal.ofReal_toReal hfinite).symm

theorem integer_entropy_summable (p : PMF ℤ) (hD : integerDispersion p ≠ ∞) :
    Summable (integerEntropyAtom p) := by
  have h := ENNReal.summable_toReal (integer_entropy_ne_top p hD)
  simpa only [ENNReal.toReal_ofReal (integerEntropyAtom_nonneg p _)] using h

theorem integerDispersion_eq_lintegral (p : PMF ℤ) :
    integerDispersion p =
      ∫⁻ z : ℤ × ℤ, ENNReal.ofReal |(z.1 : ℝ) - (z.2 : ℝ)| ∂p.toMeasure.prod p.toMeasure := by
  rw [lintegral_prod _ (measurable_of_countable _).aemeasurable]
  simp_rw [lintegral_countable', p.toMeasure_apply_singleton _ (measurableSet_singleton _)]
  dsimp [integerDispersion, integerMeanDistance]
  apply tsum_congr
  intro r
  rw [mul_comm]
  congr 1
  apply tsum_congr
  intro j
  rw [mul_comm, abs_sub_comm]

/-- Full source lemma: every probability law on the integers, with the
dispersion identified as the expected absolute difference of independent
copies. No entropy or moment finiteness assumption is imposed. -/
def WeightEntropyLemma : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ν : Measure ℤ, ∀ (_ : IsProbabilityMeasure ν),
    integerEntropy ν.toPMF ≤ ENNReal.ofReal C + extendedLogOnePlus
      (∫⁻ z : ℤ × ℤ, ENNReal.ofReal |(z.1 : ℝ) - (z.2 : ℝ)| ∂ν.prod ν)

theorem weight_entropy_lemma : WeightEntropyLemma := by
  refine ⟨weightEntropyConstant, weightEntropyConstant_pos, ?_⟩
  intro ν hν
  letI := hν
  have h := integer_entropy_dispersion ν.toPMF
  rwa [integerDispersion_eq_lintegral, Measure.toPMF_toMeasure] at h

/-- The same bound for an integer random variable on an arbitrary
probability space, using two independent samples from that space. -/
theorem weight_entropy_random_variable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Ω → ℤ) (hB : Measurable B) :
    letI := μ.isProbabilityMeasure_map hB.aemeasurable
    integerEntropy (μ.map B).toPMF ≤ ENNReal.ofReal weightEntropyConstant + extendedLogOnePlus
      (∫⁻ z : Ω × Ω, ENNReal.ofReal |(B z.1 : ℝ) - (B z.2 : ℝ)| ∂μ.prod μ) := by
  letI := μ.isProbabilityMeasure_map hB.aemeasurable
  have h := integer_entropy_dispersion (μ.map B).toPMF
  rw [integerDispersion_eq_lintegral, Measure.toPMF_toMeasure,
    Measure.map_prod_map μ μ hB hB,
    lintegral_map (measurable_of_countable _) (hB.prodMap hB)] at h
  exact h

end CircularLaw
