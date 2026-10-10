import CircularLaw.FiniteProductConditioning
import Mathlib.Probability.Independence.Basic

/-!
# Two mutually independent finite row families

Independent coordinates within each family and independence between the
two complete families give the literal product law of row pairs. This
transports the hybrid argument from its finite model to any probability space.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory

namespace CircularLaw

theorem independent_finite_families_pair_law {Ω ι α β : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure α) [IsProbabilityMeasure ν] (ρ : Measure β) [IsProbabilityMeasure ρ]
    (X : ι → Ω → α) (Y : ι → Ω → β)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXlaw : ∀ i, μ.map (X i) = ν) (hYlaw : ∀ i, μ.map (Y i) = ρ)
    (hXind : iIndepFun X μ) (hYind : iIndepFun Y μ)
    (hMutual : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ) :
    μ.map (fun ω i => (X i ω, Y i ω)) = Measure.pi (fun _ : ι => ν.prod ρ) := by
  have hXt : Measurable (fun ω i => X i ω) := measurable_pi_lambda _ hX
  have hYt : Measurable (fun ω i => Y i ω) := measurable_pi_lambda _ hY
  have hXtuple := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).mp hXind
  have hYtuple := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hY i).aemeasurable)).mp hYind
  simp_rw [hXlaw] at hXtuple
  simp_rw [hYlaw] at hYtuple
  have hPair := (indepFun_iff_map_prod_eq_prod_map_map hXt.aemeasurable hYt.aemeasurable).mp hMutual
  rw [hXtuple, hYtuple] at hPair
  let e := MeasurableEquiv.arrowProdEquivProdArrow α β ι
  have hPres := measurePreserving_arrowProdEquivProdArrow α β ι
    (fun _ => ν) (fun _ => ρ)
  have hMap : μ.map (fun ω i => (X i ω, Y i ω)) =
      (μ.map (fun ω => ((fun i => X i ω), (fun i => Y i ω)))).map e.symm := by
    rw [Measure.map_map e.symm.measurable (hXt.prodMk hYt)]
    rfl
  rw [hMap, hPair]
  exact hPres.symm.map_eq

end CircularLaw
