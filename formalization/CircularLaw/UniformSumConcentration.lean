import CircularLaw.MiroshnikovConcentration
import CircularLaw.RegularBlock

/-!
# The concentration estimates for actual uniform sample sums

The product-sum law agrees with sampling independently with replacement
from a finite set. This gives exact counting-probability interfaces for the
checked Esseen and Miroshnikov estimates.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CircularLaw

theorem finiteUniformSumLaw_eq {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (Y : α → ℂ) (m : ℕ) :
    productSumLaw (fun _ : Fin m => (finiteUniformMeasure α).map Y) =
      (finiteUniformMeasure (Fin m → α)).map (fun x => ∑ i, Y (x i)) := by
  classical
  let μ := finiteUniformMeasure (Fin m → α)
  let X := fun i (x : Fin m → α) => Y (x i)
  have hX : ∀ i, Measurable (X i) := fun _ => measurable_of_finite _
  have hInd : iIndepFun X μ := by
    dsimp only [μ, X]
    rw [finiteUniformMeasure_pi]
    exact iIndepFun_pi (fun _ => (measurable_of_finite Y).aemeasurable)
  have hLaw (i : Fin m) : μ.map (X i) = (finiteUniformMeasure α).map Y := by
    have h := (measurePreserving_eval (fun _ : Fin m => finiteUniformMeasure α) i).map_eq
    rw [← finiteUniformMeasure_pi] at h
    rw [← h, Measure.map_map (measurable_of_finite Y) (measurable_pi_apply i)]
    rfl
  have h := productSumLaw_eq_independent_sum μ X hX hInd
  simpa only [hLaw, μ, X] using h

theorem uniform_sum_probability_eq {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (Y : α → ℂ) (m : ℕ) (z : ℂ) (r : ℝ) :
    uniformProbability (fun x : Fin m → α => ‖(∑ i, Y (x i)) - z‖ ≤ r) =
      (productSumLaw (fun _ : Fin m => (finiteUniformMeasure α).map Y)).real
        (Metric.closedBall z r) := by
  rw [finiteUniformSumLaw_eq, measureReal_def,
    Measure.map_apply (measurable_of_finite _) measurableSet_closedBall]
  simpa only [Metric.closedBall, dist_eq_norm, Set.preimage_setOf_eq] using
    (finiteUniformMeasure_real (fun x : Fin m → α => ‖(∑ i, Y (x i)) - z‖ ≤ r)).symm

theorem uniform_law_concentration_le {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (Y : α → ℂ) (r A : ℝ) (hA : 0 ≤ A)
    (hBound : ∀ z, uniformProbability (fun x : α => ‖Y x - z‖ ≤ r) ≤ A) :
    planarConcentration ((finiteUniformMeasure α).map Y) r ≤ A := by
  haveI : IsProbabilityMeasure ((finiteUniformMeasure α).map Y) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite Y).aemeasurable
  apply planarConcentration_le_of_bounds _ _ _ hA
  intro z
  rw [measureReal_def, Measure.map_apply (measurable_of_finite Y) measurableSet_closedBall]
  simpa only [Metric.closedBall, dist_eq_norm, Set.preimage_setOf_eq, measureReal_def] using
    (finiteUniformMeasure_real (fun x : α => ‖Y x - z‖ ≤ r)).trans_le (hBound z)

theorem five_sixths_deficit_product_sum_small_ball {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] (hm : 1 ≤ Fintype.card ι)
    {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (hAtoms : ∀ i, planarConcentration (μ i) r₀ ≤ 5 / 6) (z : ℂ) :
    (productSumLaw μ).real (Metric.closedBall z r) ≤
      (6 * (24 * Real.exp 1 / Real.pi)) * (r / r₀) / Real.sqrt (Fintype.card ι : ℝ) := by
  have hmPos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (show 0 < Fintype.card ι by omega)
  have hrPos : 0 < r := hr₀.trans_le hr
  have hLower : (Fintype.card ι : ℝ) / 6 ≤ sumConcentrationDeficit μ r₀ := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show (1 / 6 : ℝ) ≤ 1 - planarConcentration (μ i) r₀ by linarith [hAtoms i])
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div] using h
  have hD : 0 < sumConcentrationDeficit μ r₀ := lt_of_lt_of_le (by positivity) hLower
  have hRoot : Real.sqrt (Fintype.card ι : ℝ) / 6 ≤ Real.sqrt (sumConcentrationDeficit μ r₀) := by
    have hThirtySixth : (Fintype.card ι : ℝ) / 36 ≤ sumConcentrationDeficit μ r₀ := by linarith
    have h := Real.sqrt_le_sqrt hThirtySixth
    simpa only [Real.sqrt_div hmPos.le, show Real.sqrt (36 : ℝ) = 6 by norm_num] using h
  have h := (product_sum_esseen_small_ball μ hr₀ hr hD z).trans
    (div_le_div_of_nonneg_left (by positivity : 0 ≤ (24 * Real.exp 1 / Real.pi) * (r / r₀))
      (by positivity : 0 < Real.sqrt (Fintype.card ι : ℝ) / 6) hRoot)
  convert h using 1
  ring

end CircularLaw
