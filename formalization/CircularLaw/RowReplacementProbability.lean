import CircularLaw.RowReplacementTheorem
import CircularLaw.VaryingProbabilityConvergence

/-!
# Markov bounds for the actual row replacement

The finite product of slice/Bernoulli row pairs supplies integrability.
The proved expected ridge-potential difference therefore bounds its
literal normalized deviation event. No convergence rate is assumed here.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem mean_absolute_deviation_probability_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (a : ℝ)
    (hInt : Integrable (fun x => |f x - a|) μ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {x | ε < |f x - a|} ≤ (∫ x, |f x - a| ∂μ) / ε := by
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun x => abs_nonneg (f x - a))) hInt ε
  have hSubset : {x | ε < |f x - a|} ⊆ {x | ε ≤ |f x - a|} := by
    intro x hx
    change ε < |f x - a| at hx
    exact hx.le
  apply (le_div_iff₀ hε).mpr
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hSubset) hε.le).trans hMark

theorem varying_probability_of_mean_absolute {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (f : ∀ n, Ω n → ℝ) (a : ℝ)
    (hInt : ∀ n, Integrable (fun x => |f n x - a|) (μ n))
    (hLimit : Tendsto (fun n => ∫ x, |f n x - a| ∂μ n) atTop (𝓝 0)) :
    VaryingConvergesInProbability μ f a := by
  intro ε hε
  have hUpper := hLimit.div_const ε
  simp only [zero_div] at hUpper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (Eventually.of_forall (fun _ => measureReal_nonneg))
    (Eventually.of_forall (fun n => mean_absolute_deviation_probability_bound (μ n) (f n) a (hInt n) hε))

theorem row_replacement_finite_probability_bound {n d k : ℕ}
    (hd : 0 < d) (hdn : d ≤ n) (hk : 1 ≤ k) (hkn : k < n)
    {η : ℝ} (hη : 0 < η) (u : Fin k → EuclideanSpace ℂ (Fin n))
    (hQ : 1 ≤ rowLogComparisonQ n d (n - k)) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin k => replacementRowPairLaw (show 0 < n by omega) hdn)).real
      {rows | ε < |regularizedRowPotential (rowHybridMatrix u k rows) η -
        regularizedRowPotential (rowHybridMatrix u 0 rows) η| / n} ≤
      rowReplacementErrorBound n d k η (rowShiftNormBound u) / ε := by
  let μ := Measure.pi (fun _ : Fin k => replacementRowPairLaw (show 0 < n by omega) hdn)
  let f := fun rows : Fin k → ReplacementRowPair n d => (regularizedRowPotential (rowHybridMatrix u k rows) η -
    regularizedRowPotential (rowHybridMatrix u 0 rows) η) / n
  have hnReal : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hExpected := row_replacement_finite_product hd hdn hk hkn hη u hQ
  have hMark := mean_absolute_deviation_probability_bound μ f 0 Integrable.of_finite hε
  have hIntegral : (∫ rows, |f rows - 0| ∂μ) =
      (1 / (n : ℝ)) * (∫ rows, |regularizedRowPotential (rowHybridMatrix u k rows) η -
        regularizedRowPotential (rowHybridMatrix u 0 rows) η| ∂μ) := by
    simp only [f, sub_zero, abs_div, abs_of_nonneg hnReal, integral_div]
    ring
  rw [hIntegral] at hMark
  simp only [f, sub_zero, abs_div, abs_of_nonneg hnReal] at hMark
  exact hMark.trans (div_le_div_of_nonneg_right hExpected hε.le)

end CircularLaw
