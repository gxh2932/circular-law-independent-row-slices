import CircularLaw.DensityMeasure
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The distribution of a finite independent sum

The sum law is the actual pushforward of the product of its summand laws.
Its characteristic function factors, and isolating the first coordinate
identifies the positive-dimensional law with a convolution.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Convolution BigOperators RealInnerProductSpace

namespace CircularLaw

def productSumLaw {ι : Type*} [Fintype ι] (μ : ι → Measure ℂ) : Measure ℂ :=
  (Measure.pi μ).map (fun x => ∑ i, x i)

theorem measurable_finite_sum {ι : Type*} [Fintype ι] :
    Measurable (fun x : ι → ℂ => ∑ i, x i) :=
  Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

instance productSumLaw_probability {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (productSumLaw μ) :=
  Measure.isProbabilityMeasure_map measurable_finite_sum.aemeasurable

theorem charFun_productSumLaw {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] (t : ℂ) :
    charFun (productSumLaw μ) t = ∏ i, charFun (μ i) t := by
  classical
  rw [charFun_apply, productSumLaw,
    integral_map measurable_finite_sum.aemeasurable (by fun_prop)]
  simp_rw [sum_inner, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun (_ : ι) (x : ℂ) =>
    Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I))]
  rfl

theorem productSumLaw_succ {n : ℕ} (μ : Fin (n + 1) → Measure ℂ)
    [∀ i, IsProbabilityMeasure (μ i)] :
    productSumLaw μ = μ 0 ∗ productSumLaw (fun i : Fin n => μ i.succ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
  let S : ℂ × (Fin n → ℂ) → ℂ := fun x => x.1 + ∑ i, x.2 i
  have hS : Measurable S := measurable_fst.add
    (measurable_finite_sum.comp measurable_snd)
  have hsum : (fun x : Fin (n + 1) → ℂ => ∑ i, x i) = S ∘ e := by
    funext x
    rw [Fin.sum_univ_succ]
    rfl
  have he : (Measure.pi μ).map e = (μ 0).prod (Measure.pi fun i : Fin n => μ i.succ) := by
    simpa only [e, Fin.succAbove_zero] using (measurePreserving_piFinSuccAbove μ 0).map_eq
  have hprod : (μ 0).prod ((Measure.pi fun i : Fin n => μ i.succ).map
      (fun x => ∑ i, x i)) =
      ((μ 0).prod (Measure.pi fun i : Fin n => μ i.succ)).map
        (fun x => (x.1, ∑ i, x.2 i)) := by
    simpa only [Measure.map_id, Prod.map_apply, id_eq] using
      Measure.map_prod_map (μ 0) (Measure.pi fun i : Fin n => μ i.succ)
        measurable_id measurable_finite_sum
  rw [productSumLaw, hsum, ← Measure.map_map hS e.measurable, he]
  rw [Measure.conv, productSumLaw, hprod]
  have hPair : Measurable (fun x : ℂ × (Fin n → ℂ) => (x.1, ∑ i, x.2 i)) :=
    measurable_fst.prodMk (measurable_finite_sum.comp measurable_snd)
  rw [Measure.map_map measurable_add hPair]
  rfl

theorem productSumLaw_le_volume {n : ℕ} (μ : Fin n → Measure ℂ)
    [∀ i, IsProbabilityMeasure (μ i)] (hn : 0 < n) (hμ : ∀ i, μ i ≤ volume) :
    productSumLaw μ ≤ volume := by
  cases n with
  | zero => omega
  | succ n =>
    rw [productSumLaw_succ, Measure.conv_comm]
    exact probability_conv_le_volume _ _ (hμ 0)

end CircularLaw
