import CircularLaw.GaussianShiftSpanDistance
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Conditioning on continuously varying rows before exposing a Gaussian vector

The joint span-distance event is measurable even at rank changes. Fubini
therefore transfers the uniform deterministic-subspace estimate to an
independent fresh Gaussian vector. The lower bound uses the ambient
dimension minus the number of conditioned rows, without a rank assumption.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem probability_product_event_le_sections {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (A : Set (X × Y))
    (hA : MeasurableSet A) {C : ℝ} (hC : 0 ≤ C)
    (hSections : ∀ x, ν.real (Prod.mk x ⁻¹' A) ≤ C) : (μ.prod ν).real A ≤ C := by
  have hBound : μ.prod ν A ≤ ENNReal.ofReal C := by
    rw [Measure.prod_apply hA]
    calc
      _ ≤ ∫⁻ _x, ENNReal.ofReal C ∂μ := lintegral_mono (fun x => by
        rw [← ofReal_measureReal (μ := ν)]
        exact ENNReal.ofReal_le_ofReal (hSections x))
      _ = _ := by simp
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBound
  simpa only [measureReal_def, ENNReal.toReal_ofReal hC] using h

def independentGaussianSpanDistance {ι X : Type*} [Fintype ι] {n : ℕ}
    (rows : ι → X → EuclideanSpace ℂ (Fin n)) (w : X → EuclideanSpace ℂ (Fin n))
    (p : X × (Fin n → ℂ)) : ℝ :=
  finiteSpanDistance (standardComplexGaussianVector n p.2 + w p.1) (fun i => rows i p.1)

theorem measurable_independent_gaussian_span_distance {ι X : Type*} [Fintype ι] {n : ℕ}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (rows : ι → X → EuclideanSpace ℂ (Fin n)) (w : X → EuclideanSpace ℂ (Fin n))
    (hRows : ∀ i, Continuous (rows i)) (hw : Continuous w) :
    Measurable (independentGaussianSpanDistance rows w) :=
  measurable_finite_span_distance _ _
    (((standardComplexGaussianVector_continuous n).comp continuous_snd).add (hw.comp continuous_fst))
    (fun i => (hRows i).comp continuous_fst)

theorem independent_gaussian_span_distance_lower_eighth_tail {ι X : Type*} [Fintype ι] {n : ℕ}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (rows : ι → X → EuclideanSpace ℂ (Fin n)) (w : X → EuclideanSpace ℂ (Fin n))
    (hRows : ∀ i, Continuous (rows i)) (hw : Continuous w) (hCard : Fintype.card ι < n) :
    (μ.prod (standardComplexGaussianVectorLaw n)).real
      {p | independentGaussianSpanDistance rows w p ^ 2 ≤ (n - Fintype.card ι : ℕ) / (8 : ℝ)} ≤
        (1 / 2 : ℝ) ^ (n - Fintype.card ι) := by
  apply probability_product_event_le_sections μ (standardComplexGaussianVectorLaw n) _
    (measurableSet_le ((measurable_independent_gaussian_span_distance rows w hRows hw).pow_const 2)
      measurable_const) (by positivity)
  intro x
  have hDim := finite_span_orthogonal_finrank_lower (fun i => rows i x)
  apply (measureReal_mono (μ := standardComplexGaussianVectorLaw n) (s₂ :=
    {z | finiteSpanDistance (standardComplexGaussianVector n z + w x) (fun i => rows i x) ^ 2 ≤
      (Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i => rows i x)))ᗮ : ℝ) / 8}) ?_).trans
    ((shifted_gaussian_finite_span_distance_lower_eighth_tail (fun i => rows i x) hCard (w x)).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hDim))
  intro z hz
  change finiteSpanDistance (standardComplexGaussianVector n z + w x) (fun i => rows i x) ^ 2 ≤ _ at hz ⊢
  exact hz.trans (div_le_div_of_nonneg_right (by exact_mod_cast hDim) (by norm_num))

theorem independent_gaussian_span_distance_zero {ι X : Type*} [Fintype ι] {n : ℕ}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (rows : ι → X → EuclideanSpace ℂ (Fin n)) (w : X → EuclideanSpace ℂ (Fin n))
    (hRows : ∀ i, Continuous (rows i)) (hw : Continuous w) (hCard : Fintype.card ι < n) :
    μ.prod (standardComplexGaussianVectorLaw n)
      {p | independentGaussianSpanDistance rows w p = 0} = 0 := by
  apply Measure.measure_prod_null_of_ae_null
    (measurableSet_eq_fun (measurable_independent_gaussian_span_distance rows w hRows hw) measurable_const)
  exact ae_of_all μ (fun x => shifted_gaussian_finite_span_distance_zero (fun i => rows i x) hCard (w x))

theorem independent_gaussian_span_distance_pos_ae {ι X : Type*} [Fintype ι] {n : ℕ}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (rows : ι → X → EuclideanSpace ℂ (Fin n)) (w : X → EuclideanSpace ℂ (Fin n))
    (hRows : ∀ i, Continuous (rows i)) (hw : Continuous w) (hCard : Fintype.card ι < n) :
    ∀ᵐ p ∂μ.prod (standardComplexGaussianVectorLaw n), 0 < independentGaussianSpanDistance rows w p := by
  rw [ae_iff]
  apply measure_mono_null (t := {p | independentGaussianSpanDistance rows w p = 0})
    (fun p hp => le_antisymm (le_of_not_gt hp) (finite_span_distance_nonneg _ _))
    (independent_gaussian_span_distance_zero μ rows w hRows hw hCard)

end CircularLaw
