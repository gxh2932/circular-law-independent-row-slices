import CircularLaw.EntropyCancellation
import CircularLaw.MeasureModel
import CircularLaw.MaxWeight

/-!
# Weight entropy for a uniform coordinate

The source dyadic weight law is the pushforward of a uniform coordinate.
Repeated integer weights aggregate their masses. Its dispersion is exactly
the finite pair mean used by the checked row-profile estimates.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace CircularLaw

def uniformIntegerLaw {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (B : α → ℤ) : PMF ℤ :=
  letI := (finiteUniformMeasure α).isProbabilityMeasure_map
    (measurable_of_countable B).aemeasurable
  ((finiteUniformMeasure α).map B).toPMF

theorem uniformIntegerLaw_toMeasure {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (B : α → ℤ) :
    (uniformIntegerLaw B).toMeasure = (finiteUniformMeasure α).map B := by
  letI := (finiteUniformMeasure α).isProbabilityMeasure_map
    (measurable_of_countable B).aemeasurable
  dsimp [uniformIntegerLaw]
  exact Measure.toPMF_toMeasure _

theorem uniformIntegerLaw_apply {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (B : α → ℤ) (j : ℤ) :
    uniformIntegerLaw B j = ENNReal.ofReal (uniformProbability (fun a => B a = j)) := by
  change ((finiteUniformMeasure α).map B) {j} = _
  rw [Measure.map_apply (measurable_of_countable B) (measurableSet_singleton j)]
  exact finiteUniformMeasure_apply (fun a => B a = j)

theorem uniformIntegerLaw_dispersion {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (B : α → ℤ) :
    integerDispersion (uniformIntegerLaw B) =
      ENNReal.ofReal (pairDispersion (fun a => (B a : ℝ))) := by
  rw [integerDispersion_eq_lintegral, uniformIntegerLaw_toMeasure,
    Measure.map_prod_map _ _ (measurable_of_countable B) (measurable_of_countable B),
    lintegral_map (measurable_of_countable _)
      ((measurable_of_countable B).prodMap (measurable_of_countable B))]
  rw [← ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
    (ae_of_all _ (fun _ => abs_nonneg _))]
  congr 1
  rw [integral_prod _ Integrable.of_finite]
  simp_rw [integral_finiteUniformMeasure]
  calc
    (finiteMean fun x => finiteMean fun y =>
        |(B x : ℝ) - (B y : ℝ)|) =
        finiteMean (fun z : α × α => |(B z.2 : ℝ) - (B z.1 : ℝ)|) :=
      (finiteMean_prod_fubini (fun z : α × α => |(B z.2 : ℝ) - (B z.1 : ℝ)|)).symm
    _ = pairDispersion (fun a => (B a : ℝ)) := by
      unfold pairDispersion
      congr 1
      funext z
      exact abs_sub_comm _ _

theorem uniformIntegerLaw_dispersion_ne_top {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (B : α → ℤ) :
    integerDispersion (uniformIntegerLaw B) ≠ ∞ := by
  rw [uniformIntegerLaw_dispersion]
  exact ENNReal.ofReal_ne_top

theorem uniform_integer_entropy_bound {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (B : α → ℤ) :
    (∑' j : ℤ, integerEntropyAtom (uniformIntegerLaw B) j) ≤
      weightEntropyConstant + Real.log (1 + pairDispersion (fun a => (B a : ℝ))) := by
  have h := integer_entropy_real_bound (uniformIntegerLaw B) (uniformIntegerLaw_dispersion_ne_top B)
  rwa [uniformIntegerLaw_dispersion, ENNReal.toReal_ofReal (pairDispersion_nonneg _)] at h

theorem uniform_integer_compression_cancel {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {c n K A M : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n) (hK : n / 2 ≤ K) (B : α → ℤ)
    (hCompression : M ≤ Real.exp (A * n +
      n * ∑' j : ℤ, integerEntropyAtom (uniformIntegerLaw B) j)) :
    M * Real.exp (-c * K * pairDispersion (fun a => (B a : ℝ))) ≤
      Real.exp ((A + entropyPenaltyConstant (c / 2)) * n) := by
  have h := integer_entropy_compression_cancel hc hn hK (uniformIntegerLaw B)
    (uniformIntegerLaw_dispersion_ne_top B) hCompression
  rwa [uniformIntegerLaw_dispersion, ENNReal.toReal_ofReal (pairDispersion_nonneg _)] at h

end CircularLaw
