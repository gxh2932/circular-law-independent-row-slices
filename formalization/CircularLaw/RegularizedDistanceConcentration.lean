import CircularLaw.ConvexProductConcentrationProof
import CircularLaw.FiniteLawMedian
import CircularLaw.BernoulliSliceTransfer

/-!
# Full regularized distance concentration

The actual independent Bernoulli law has bounded complex coordinates.
Finite-law median existence discharges the median used by the checked
convex theorem. Exact conditioning and its Stirling mass lower bound
give the square-root-degree slice loss. The comparison with the literal
second-moment scale is supplied by the checked fourth-moment argument.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace CircularLaw

theorem regularizedDistance_bernoulli_mean_tail {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsPositiveMatrixContraction P)
    (p : ℝ≥0) (hp : p ≤ 1) (η : ℝ) (u : EuclideanSpace ℂ (Fin n))
    {t : ℝ} (ht : 0 < t) :
    (bernoulliCubeLaw (Fin n) p hp).real
      {x | t ≤ |regularizedDistance P η u (bernoulliCubeVector x) - regularizedDistanceMean P η u p hp|} ≤
      (4 * Real.exp 16) * Real.exp (-(1 / 1024) * t ^ 2) := by
  let μ := bernoulliCubeLaw (Fin n) p hp
  let X := fun i : Fin n => fun x : Fin n → Bool => (cond (x i) 1 0 : ℂ)
  have hX : ∀ i, Measurable (X i) := fun i => measurable_of_countable (X i)
  have hInd : iIndepFun X μ := iIndepFun_pi
    (fun _ => (measurable_of_countable (fun b : Bool => (cond b 1 0 : ℂ))).aemeasurable)
  have hBound : ∀ i, ∀ᵐ x ∂μ, ‖X i x‖ ≤ (1 : ℝ) := by
    intro i
    apply ae_of_all
    intro x
    dsimp only [X]
    cases x i <;> simp
  obtain ⟨m, hMedian⟩ := finite_law_median_exists μ
    (fun x => regularizedDistance P η u (complexCoordinateVector X x))
  have h := convex_product_mean_tail μ X hX hInd (by norm_num : (0 : ℝ) < 1) hBound
    (regularizedDistance_convex hP.1 η u) (regularizedDistance_lipschitz hP η u) m hMedian ht
  simpa only [mul_one, μ, X, complexCoordinateVector, bernoulliCubeVector, regularizedDistanceMean] using h

theorem regularizedDistance_slice_mean_tail {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsPositiveMatrixContraction P)
    (η : ℝ) (u : EuclideanSpace ℂ (Fin n)) {t : ℝ} (ht : 0 < t) :
    (rowSliceLaw n d).real
      {s | t ≤ |regularizedDistance P η u (rowSliceEuclideanRow s) -
        regularizedDistanceMean P η u (rowBernoulliParameter n d)
          (rowBernoulliParameter_le_one (by omega) hdn)|} ≤
      (4 * Real.exp 1 ^ 2 * (4 * Real.exp 16)) * Real.sqrt (d : ℝ) *
        Real.exp (-(1 / 1024) * t ^ 2) := by
  let p := rowBernoulliParameter n d
  let hp := rowBernoulliParameter_le_one (show 0 < n by omega) hdn
  have hTail := regularizedDistance_bernoulli_mean_tail hP p hp η u ht
  exact regularizedDistance_slice_tail_of_bernoulli hd hdn P η u
    (regularizedDistanceMean P η u p hp) t (4 * Real.exp 16) (1 / 1024) hTail

/-- Source lemma in the standing positive-degree row-slice setting, with
    literal mean and second-moment scale and absolute constants. -/
def RegularizedDistanceConcentrationLemma : Prop :=
  ∃ c₀ c C : ℝ, 0 < c₀ ∧ 0 < c ∧ 0 < C ∧
    ∀ (n d : ℕ) (hd : 0 < d) (hdn : d ≤ n)
      (P : Matrix (Fin n) (Fin n) ℂ), IsPositiveMatrixContraction P →
    ∀ (η : ℝ), 0 < η → ∀ (u : EuclideanSpace ℂ (Fin n)),
    let p := rowBernoulliParameter n d
    let hp := rowBernoulliParameter_le_one (show 0 < n by omega) hdn
    1 ≤ regularizedDistanceScale P η u p →
      (c₀ * regularizedDistanceScale P η u p ≤ regularizedDistanceMean P η u p hp ∧
        regularizedDistanceMean P η u p hp ≤ regularizedDistanceScale P η u p) ∧
      ∀ (t : ℝ), 0 < t →
        (bernoulliCubeLaw (Fin n) p hp).real
          {x | t ≤ |regularizedDistance P η u (bernoulliCubeVector x) - regularizedDistanceMean P η u p hp|} ≤
          C * Real.exp (-c * t ^ 2) ∧
        (rowSliceLaw n d).real
          {s | t ≤ |regularizedDistance P η u (rowSliceEuclideanRow s) - regularizedDistanceMean P η u p hp|} ≤
          C * Real.sqrt (d : ℝ) * Real.exp (-c * t ^ 2)

theorem regularized_distance_concentration_lemma : RegularizedDistanceConcentrationLemma := by
  refine ⟨1 / 8, 1 / 1024, 4 * Real.exp 1 ^ 2 * (4 * Real.exp 16),
    by norm_num, by norm_num, by positivity, ?_⟩
  intro n d hd hdn P hP η _hη u p hp hScale
  refine ⟨?_, ?_⟩
  · have hComparison := regularizedDistanceMean_comparison hP p hp η u hScale
    constructor
    · nlinarith [hComparison.1]
    · exact hComparison.2
  · intro t ht
    refine ⟨?_, regularizedDistance_slice_mean_tail hd hdn hP η u ht⟩
    have h := regularizedDistance_bernoulli_mean_tail hP p hp η u ht
    apply h.trans
    have hExp : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    have hFactor : 1 ≤ 4 * Real.exp 1 ^ 2 := by nlinarith
    have hMul := mul_le_mul_of_nonneg_right hFactor
      (show 0 ≤ (4 * Real.exp 16) * Real.exp (-(1 / 1024) * t ^ 2) from by positivity)
    nlinarith

end CircularLaw
