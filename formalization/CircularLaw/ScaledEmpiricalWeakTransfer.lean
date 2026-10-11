import CircularLaw.RelativeEmpiricalWeakTransfer
import CircularLaw.SquareSingularPerturbationBounds

/-!
# Empirical weak laws under convergent scales and scalar shifts

A fixed positive scale pushes the limiting measure forward. Convergent
scales and vanishing scalar shifts produce a relative pointwise error,
which the compact limiting support controls without bounding every sample.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped NNReal Topology

namespace CircularLaw

theorem empirical_weak_convergence_map_continuous {Ω : ℕ → Type*} {q : ℕ → ℕ}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    (s : ∀ n, Ω n → Fin (q n) → ℝ≥0) (ν : Measure ℝ≥0)
    (g : ℝ≥0 → ℝ≥0) (hg : Continuous g)
    (hWeak : EmpiricalWeakConvergenceInProbability μ s ν) :
    EmpiricalWeakConvergenceInProbability μ (fun n x i => g (s n x i)) (ν.map g) := by
  intro f hf hBound
  have h := hWeak (fun t => f (g t)) (hf.comp hg)
    (by obtain ⟨M, hM⟩ := hBound; exact ⟨M, fun t => hM (g t)⟩)
  rw [integral_map_of_stronglyMeasurable hg.measurable hf.stronglyMeasurable]
  exact h

theorem scaled_nonnegative_measure_support (ν : Measure ℝ≥0) {c R : ℝ}
    (hc : 0 < c) (hSupport : ν {t : ℝ≥0 | R < (t : ℝ)} = 0) :
    (ν.map (fun t : ℝ≥0 => Real.toNNReal c * t))
      {t : ℝ≥0 | c * R < (t : ℝ)} = 0 := by
  have hg : Measurable (fun t : ℝ≥0 => Real.toNNReal c * t) :=
    (continuous_const.mul continuous_id).measurable
  have hs : MeasurableSet {t : ℝ≥0 | c * R < (t : ℝ)} :=
    measurableSet_lt measurable_const NNReal.continuous_coe.measurable
  rw [Measure.map_apply hg hs]
  have hSet : (fun t : ℝ≥0 => Real.toNNReal c * t) ⁻¹'
      {t : ℝ≥0 | c * R < (t : ℝ)} = {t : ℝ≥0 | R < (t : ℝ)} := by
    ext t
    change c * R < (Real.toNNReal c * t : ℝ≥0).toReal ↔ R < (t : ℝ)
    rw [NNReal.coe_mul, Real.coe_toNNReal c hc.le]
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith
  rw [hSet]
  exact hSupport

theorem ordered_square_singular_scale_shift_relative_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r)
    (w : ℂ) (j : Fin n) :
    |orderedSquareSingularValues ((r : ℂ) • A + w • 1) j -
      c * orderedSquareSingularValues A j| ≤
      (|r - c| / c + ‖w‖) * (1 + c * orderedSquareSingularValues A j) := by
  have hShift := ordered_square_singular_scalar_shift_abs_bound ((r : ℂ) • A) w j
  rw [ordered_square_singular_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at hShift
  have hTriangle := abs_sub_le
    (orderedSquareSingularValues ((r : ℂ) • A + w • 1) j)
    (r * orderedSquareSingularValues A j) (c * orderedSquareSingularValues A j)
  have hMul : |r * orderedSquareSingularValues A j - c * orderedSquareSingularValues A j| =
      |r - c| * orderedSquareSingularValues A j := by
    rw [← sub_mul, abs_mul, abs_of_nonneg (orderedSquareSingularValues_nonneg A j)]
  rw [hMul] at hTriangle
  have hRatio : |r - c| / c * c = |r - c| := div_mul_cancel₀ _ hc.ne'
  have hExtra := mul_nonneg (norm_nonneg w)
    (mul_nonneg hc.le (orderedSquareSingularValues_nonneg A j))
  have hRatioNonneg : 0 ≤ |r - c| / c := div_nonneg (abs_nonneg _) hc.le
  have hRatioProduct := congrArg (fun t : ℝ => t * orderedSquareSingularValues A j) hRatio
  nlinarith

theorem empirical_square_singular_weak_convergence_scale_shift {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (q : ℕ → ℕ) (hQ : Tendsto q atTop atTop)
    (A : ∀ n, Ω n → Matrix (Fin (q n)) (Fin (q n)) ℂ) (ν : Measure ℝ≥0)
    (R : ℝ) (hR : 0 ≤ R) (hSupport : ν {t : ℝ≥0 | R < (t : ℝ)} = 0)
    (r : ℕ → ℝ) (w : ℕ → ℂ) {c : ℝ} (hc : 0 < c)
    (hrNonneg : ∀ n, 0 ≤ r n) (hr : Tendsto r atTop (𝓝 c))
    (hw : Tendsto w atTop (𝓝 0))
    (hWeak : EmpiricalWeakConvergenceInProbability μ
      (fun n x => squareSingularValuesNNReal (A n x)) ν) :
    EmpiricalWeakConvergenceInProbability μ
      (fun n x => squareSingularValuesNNReal ((r n : ℂ) • A n x + w n • 1))
      (ν.map (fun t : ℝ≥0 => Real.toNNReal c * t)) := by
  have hScaled := empirical_weak_convergence_map_continuous μ
    (fun n x => squareSingularValuesNNReal (A n x)) ν
    (fun t : ℝ≥0 => Real.toNNReal c * t) (continuous_const.mul continuous_id) hWeak
  let delta := fun n => |r n - c| / c + ‖w n‖
  have hDeltaNonneg (n : ℕ) : 0 ≤ delta n := by dsimp [delta]; positivity
  have hDelta : Tendsto delta atTop (𝓝 0) := by
    have h := ((hr.sub_const c).abs.div_const c).add hw.norm
    simpa only [sub_self, abs_zero, zero_div, norm_zero, add_zero] using h
  exact empirical_weak_convergence_of_relative_pointwise_error μ q hQ
    (fun n x => squareSingularValuesNNReal ((r n : ℂ) • A n x + w n • 1))
    (fun n x i => Real.toNNReal c * squareSingularValuesNNReal (A n x) i)
    (ν.map (fun t : ℝ≥0 => Real.toNNReal c * t)) (c * R) (mul_nonneg hc.le hR)
    (scaled_nonnegative_measure_support ν hc hSupport) delta hDeltaNonneg hDelta
    (Eventually.of_forall (fun n x i => by
      simpa only [squareSingularValuesNNReal, NNReal.coe_mul, Real.coe_toNNReal c hc.le] using
        ordered_square_singular_scale_shift_relative_bound (A n x) hc (hrNonneg n) (w n) i)) hScaled

end CircularLaw
