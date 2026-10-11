import CircularLaw.GaussianShiftProjectionNorm
import CircularLaw.FiniteSpanDistanceMeasurable
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Distance of a shifted Gaussian vector from every finite row span

The distance is the norm of its projection onto the orthogonal complement.
The complement has dimension at least the ambient dimension minus the
number of spanning rows. Its shifted Gaussian small-ball estimate is
uniform over the actual rows and the deterministic shift. A positive
complement dimension also makes the zero-distance event null.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem finite_span_distance_eq_projection_norm {ι : Type*} [Fintype ι] {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) (rows : ι → EuclideanSpace ℂ (Fin n)) :
    finiteSpanDistance v rows = ‖(Submodule.span ℂ (Set.range rows))ᗮ.starProjection v‖ := by
  symm
  rw [Submodule.starProjection_orthogonal]
  change ‖v - (Submodule.span ℂ (Set.range rows)).starProjection v‖ =
    Metric.infDist v (Submodule.span ℂ (Set.range rows) : Set (EuclideanSpace ℂ (Fin n)))
  rw [Submodule.starProjection_minimal, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl

theorem finite_span_orthogonal_finrank_lower {ι : Type*} [Fintype ι] {n : ℕ}
    (rows : ι → EuclideanSpace ℂ (Fin n)) :
    n - Fintype.card ι ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range rows))ᗮ := by
  let E := Submodule.span ℂ (Set.range rows)
  have hRank : Module.finrank ℂ E ≤ Fintype.card ι := finrank_range_le_card rows
  have hDim := E.finrank_add_finrank_orthogonal
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hDim
  change Module.finrank ℂ (Submodule.span ℂ (Set.range rows)) +
    Module.finrank ℂ (Submodule.span ℂ (Set.range rows))ᗮ = n at hDim
  change Module.finrank ℂ (Submodule.span ℂ (Set.range rows)) ≤ Fintype.card ι at hRank
  omega

theorem shifted_gaussian_finite_span_distance_smallBall {ι : Type*} [Fintype ι] {n : ℕ}
    (rows : ι → EuclideanSpace ℂ (Fin n)) (hRows : Fintype.card ι < n)
    (w : EuclideanSpace ℂ (Fin n)) {u : ℝ} (hu : 0 < u) :
    (standardComplexGaussianVectorLaw n).real
      {z | finiteSpanDistance (standardComplexGaussianVector n z + w) rows ^ 2 ≤ u} ≤
        (Real.exp 1 * u / Module.finrank ℂ (Submodule.span ℂ (Set.range rows))ᗮ) ^
          Module.finrank ℂ (Submodule.span ℂ (Set.range rows))ᗮ := by
  simp only [finite_span_distance_eq_projection_norm]
  exact projectedComplexGaussian_shift_normSq_smallBall _
    ((Nat.sub_pos_of_lt hRows).trans_le (finite_span_orthogonal_finrank_lower rows)) w hu

theorem shifted_gaussian_finite_span_distance_lower_eighth_tail {ι : Type*} [Fintype ι] {n : ℕ}
    (rows : ι → EuclideanSpace ℂ (Fin n)) (hRows : Fintype.card ι < n)
    (w : EuclideanSpace ℂ (Fin n)) :
    (standardComplexGaussianVectorLaw n).real
      {z | finiteSpanDistance (standardComplexGaussianVector n z + w) rows ^ 2 ≤
        (Module.finrank ℂ (Submodule.span ℂ (Set.range rows))ᗮ : ℝ) / 8} ≤
          (1 / 2 : ℝ) ^ Module.finrank ℂ (Submodule.span ℂ (Set.range rows))ᗮ := by
  simp only [finite_span_distance_eq_projection_norm]
  exact subspaceGaussian_shift_normSq_lower_eighth_tail _
    ((Nat.sub_pos_of_lt hRows).trans_le (finite_span_orthogonal_finrank_lower rows)) w

theorem shifted_gaussian_finite_span_distance_zero {ι : Type*} [Fintype ι] {n : ℕ}
    (rows : ι → EuclideanSpace ℂ (Fin n)) (hRows : Fintype.card ι < n)
    (w : EuclideanSpace ℂ (Fin n)) :
    standardComplexGaussianVectorLaw n
      {z | finiteSpanDistance (standardComplexGaussianVector n z + w) rows = 0} = 0 := by
  let p := Module.finrank ℂ (Submodule.span ℂ (Set.range rows))ᗮ
  have hp : 0 < p := (Nat.sub_pos_of_lt hRows).trans_le (finite_span_orthogonal_finrank_lower rows)
  have hLimit : Tendsto (fun k : ℕ =>
      (Real.exp 1 * (1 / ((k : ℝ) + 1)) / (p : ℝ)) ^ p) atTop (𝓝 0) := by
    have h := (((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.exp 1)).div_const
      (p : ℝ)).pow p
    simpa only [mul_zero, zero_div, zero_pow hp.ne'] using h
  have hLe (k : ℕ) : (standardComplexGaussianVectorLaw n).real
      {z | finiteSpanDistance (standardComplexGaussianVector n z + w) rows = 0} ≤
        (Real.exp 1 * (1 / ((k : ℝ) + 1)) / (p : ℝ)) ^ p := by
    apply (measureReal_mono (μ := standardComplexGaussianVectorLaw n) (s₂ :=
      {z | finiteSpanDistance (standardComplexGaussianVector n z + w) rows ^ 2 ≤
        1 / ((k : ℝ) + 1)}) ?_).trans
      (shifted_gaussian_finite_span_distance_smallBall rows hRows w (by positivity))
    intro z hz
    change finiteSpanDistance (standardComplexGaussianVector n z + w) rows = 0 at hz
    change finiteSpanDistance (standardComplexGaussianVector n z + w) rows ^ 2 ≤ 1 / ((k : ℝ) + 1)
    simpa only [hz, zero_pow (by norm_num : 2 ≠ 0)] using
      (one_div_nonneg.mpr (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1))
  have hZero : (standardComplexGaussianVectorLaw n).real
      {z | finiteSpanDistance (standardComplexGaussianVector n z + w) rows = 0} = 0 :=
    tendsto_nhds_unique tendsto_const_nhds
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLimit
        (fun _ => measureReal_nonneg) hLe)
  exact (measureReal_eq_zero_iff (μ := standardComplexGaussianVectorLaw n)).mp hZero

theorem shifted_gaussian_not_mem_finite_span {ι : Type*} [Fintype ι] {n : ℕ}
    (rows : ι → EuclideanSpace ℂ (Fin n)) (hRows : Fintype.card ι < n)
    (w : EuclideanSpace ℂ (Fin n)) :
    ∀ᵐ z ∂standardComplexGaussianVectorLaw n,
      standardComplexGaussianVector n z + w ∉ Submodule.span ℂ (Set.range rows) := by
  rw [ae_iff]
  apply measure_mono_null (t := {z | finiteSpanDistance (standardComplexGaussianVector n z + w) rows = 0})
    (fun z hz => Metric.infDist_zero_of_mem (by simpa only [not_not] using hz))
    (shifted_gaussian_finite_span_distance_zero rows hRows w)

end CircularLaw
