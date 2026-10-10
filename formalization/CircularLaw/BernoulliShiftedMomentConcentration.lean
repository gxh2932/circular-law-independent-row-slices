import CircularLaw.BernoulliWordConcentration
import CircularLaw.BernoulliShiftedMomentMeanLimits
import CircularLaw.VaryingProbabilityPolynomial

/-!
# Actual centered shifted Bernoulli singular moments concentrate

At every complex shift and every even order, the actual empirical
singular moment is a finite real weighted sum of centered word traces.
Their checked convergence in probability gives convergence of this
actual moment to its scalar-shifted pattern-count limit. Identification
with the Gaussian moment remains a separate obligation.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

def bernoulliCenteredShiftedSingularMoment {n : ℕ} (d : ℕ) (z : ℂ) (k : ℕ)
    (x : BernoulliSquareSample n) : ℝ :=
  ∫ t, (t : ℝ) ^ (2 * k)
    ∂squareSingularMeasure (normalizedCenteredBernoulliMatrix d x - z • 1)

theorem bernoulli_centered_shifted_moment_word_sum {n : ℕ} (d : ℕ) (z : ℂ) (k : ℕ)
    (x : BernoulliSquareSample n) :
    bernoulliCenteredShiftedSingularMoment d z k x =
      ((scalarShiftWordExpansion z (gramMatrixWord k)).map
        (fun q => q.1.re * bernoulliNormalizedWordTrace d q.2 x)).sum := by
  have hIm (w : List Bool) :
      (matrixAdjointWord (normalizedCenteredBernoulliMatrix d x) w).trace.im = 0 := by
    rw [bernoulli_normalized_word_trace_eq_real]
    rfl
  have hList (L : List (ℂ × List Bool)) :
      ((L.map (fun q => q.1 *
        (matrixAdjointWord (normalizedCenteredBernoulliMatrix d x) q.2).trace)).sum).re / n =
          (L.map (fun q => q.1.re * bernoulliNormalizedWordTrace d q.2 x)).sum := by
    induction L with
    | nil => simp
    | cons q L ih =>
      simp only [List.map_cons, List.sum_cons, Complex.add_re, add_div, ih,
        Complex.mul_re, hIm, mul_zero, sub_zero, bernoulliNormalizedWordTrace]
      ring
  rw [bernoulliCenteredShiftedSingularMoment, square_singular_measure_even_moment,
    matrix_shifted_gram_pow_word, matrix_scalar_shifted_word_expansion, Matrix.trace_list_sum]
  simp only [List.map_map]
  change ((List.map (fun q =>
    (q.1 • matrixAdjointWord (normalizedCenteredBernoulliMatrix d x) q.2).trace)
      (scalarShiftWordExpansion z (gramMatrixWord k))).sum).re / n = _
  simp only [Matrix.trace_smul, smul_eq_mul]
  exact hList _

theorem bernoulli_shifted_moment_limit_real_word_sum (z : ℂ) (k : ℕ) :
    (bernoulliShiftedMomentMeanLimit z k).re =
      ((scalarShiftWordExpansion z (gramMatrixWord k)).map
        (fun q => q.1.re * (bernoulliWordMeanLimit q.2 : ℝ))).sum := by
  have hList (L : List (ℂ × List Bool)) :
      ((L.map (fun q => q.1 * (bernoulliWordMeanLimit q.2 : ℂ))).sum).re =
        (L.map (fun q => q.1.re * (bernoulliWordMeanLimit q.2 : ℝ))).sum := by
    induction L with
    | nil => simp
    | cons q L ih =>
      simp only [List.map_cons, List.sum_cons, Complex.add_re, ih,
        Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
  exact hList _

theorem bernoulli_weighted_word_list_converges_in_probability (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (L : List (ℂ × List Bool)) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n x => (L.map (fun q => q.1.re * bernoulliNormalizedWordTrace (d n) q.2 x)).sum)
      (L.map (fun q => q.1.re * (bernoulliWordMeanLimit q.2 : ℝ))).sum := by
  induction L with
  | nil => simpa only [List.map_nil, List.sum_nil] using
      varying_probability_const (fun n => sparseBernoulliMatrixLaw n (d n)) 0
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact varying_probability_add _
      (varying_probability_mul_deterministic _
        (bernoulli_word_converges_in_probability d hDegree hSparse q.2) tendsto_const_nhds) ih

theorem bernoulli_centered_shifted_moment_converges_in_probability (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop)
    (hSparse : Tendsto (fun n => (d n : ℝ) / n) atTop (𝓝 0)) (z : ℂ) (k : ℕ) :
    VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n))
      (fun n => bernoulliCenteredShiftedSingularMoment (d n) z k)
      (bernoulliShiftedMomentMeanLimit z k).re := by
  have hFun : (fun n => bernoulliCenteredShiftedSingularMoment (n := n) (d n) z k) =
      (fun n (x : BernoulliSquareSample n) => ((scalarShiftWordExpansion z (gramMatrixWord k)).map
        (fun q => q.1.re * bernoulliNormalizedWordTrace (d n) q.2 x)).sum) := by
    funext n x
    exact bernoulli_centered_shifted_moment_word_sum (d n) z k x
  rw [hFun, bernoulli_shifted_moment_limit_real_word_sum]
  exact bernoulli_weighted_word_list_converges_in_probability d hDegree hSparse
    (scalarShiftWordExpansion z (gramMatrixWord k))

end CircularLaw
