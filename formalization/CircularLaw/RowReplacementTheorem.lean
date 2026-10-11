import CircularLaw.RowReplacementTelescoping
import CircularLaw.IndependentFiniteFamilies

/-!
# Full generalized regularized row replacement

The theorem retains the actual independent slice rows, independent
Bernoulli rows, mutual independence of the two families, deterministic
shifts, arbitrary `1 ≤ k < n`, positive regularization, and `Q ≥ 1`.
All conditioning, determinant and comparison inputs are proved.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory

namespace CircularLaw

def shiftedSliceRows {n d k : ℕ} (u : Fin k → EuclideanSpace ℂ (Fin n))
    (rows : Fin k → RowSlice n d) : Matrix (Fin k) (Fin n) ℂ :=
  fun i j => (rowSliceEuclideanRow (rows i) + u i) j

def shiftedBernoulliRows {n k : ℕ} (u : Fin k → EuclideanSpace ℂ (Fin n))
    (rows : Fin k → (Fin n → Bool)) : Matrix (Fin k) (Fin n) ℂ :=
  fun i j => (bernoulliCubeVector (rows i) + u i) j

theorem row_replacement_expected_bound {Ω : Type*} [MeasurableSpace Ω]
    {n d k : ℕ} (hd : 0 < d) (hdn : d ≤ n) (hk : 1 ≤ k) (hkn : k < n)
    {η : ℝ} (hη : 0 < η) (u : Fin k → EuclideanSpace ℂ (Fin n))
    (hQ : 1 ≤ rowLogComparisonQ n d (n - k))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin k → Ω → RowSlice n d) (Y : Fin k → Ω → (Fin n → Bool))
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXlaw : ∀ i, μ.map (X i) = rowSliceLaw n d)
    (hYlaw : ∀ i, μ.map (Y i) = bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
      (rowBernoulliParameter_le_one (by omega) hdn))
    (hXind : iIndepFun X μ) (hYind : iIndepFun Y μ)
    (hMutual : IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ) :
    (1 / (n : ℝ)) *
      (∫ ω, |regularizedRowPotential (shiftedSliceRows u (fun i => X i ω)) η -
        regularizedRowPotential (shiftedBernoulliRows u (fun i => Y i ω)) η| ∂μ) ≤
      rowReplacementErrorBound n d k η (rowShiftNormBound u) := by
  haveI := rowSliceLaw_probability hdn
  have hPair := independent_finite_families_pair_law μ (rowSliceLaw n d)
    (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
      (rowBernoulliParameter_le_one (by omega) hdn)) X Y hX hY hXlaw hYlaw hXind hYind hMutual
  have hMeas : Measurable (fun ω i => (X i ω, Y i ω)) :=
    measurable_pi_lambda _ (fun i => (hX i).prodMk (hY i))
  have hTransport :
      (∫ ω, |regularizedRowPotential (shiftedSliceRows u (fun i => X i ω)) η -
        regularizedRowPotential (shiftedBernoulliRows u (fun i => Y i ω)) η| ∂μ) =
      ∫ rows, |regularizedRowPotential (rowHybridMatrix u k rows) η -
        regularizedRowPotential (rowHybridMatrix u 0 rows) η|
        ∂Measure.pi (fun _ : Fin k => replacementRowPairLaw (by omega) hdn) := by
    simpa only [rowHybridMatrix_full, rowHybridMatrix_zero, shiftedSliceRows, shiftedBernoulliRows,
      replacementRowPairLaw] using
      finite_law_integral_comp hMeas hPair
        (fun rows => |regularizedRowPotential (rowHybridMatrix u k rows) η -
          regularizedRowPotential (rowHybridMatrix u 0 rows) η|)
  rw [hTransport]
  exact row_replacement_finite_product hd hdn hk hkn hη u hQ

theorem rowReplacementErrorBound_le_common (n d k : ℕ) {η : ℝ} (hη : 0 < η) (R : ℝ) :
    rowReplacementErrorBound n d k η R ≤
      (10000 + 2 * rowDistanceTailConstant) *
          Real.sqrt (Real.log (Real.exp 1 * (d : ℝ)) / rowLogComparisonQ n d (n - k)) +
        (10000 + 2 * rowDistanceTailConstant) * Real.sqrt (d : ℝ) *
          Real.log (rowReplacementUpperBound n η R / η) *
            Real.exp (-(1 / 262144) * rowLogComparisonQ n d (n - k)) := by
  have hLog : 0 ≤ Real.log (rowReplacementUpperBound n η R / η) :=
    Real.log_nonneg ((one_le_div hη).mpr (rowReplacementUpperBound_ge_regularization n hη R))
  have hPref : 0 ≤ rowDistanceTailConstant := by dsimp [rowDistanceTailConstant]; positivity
  have hGood := mul_le_mul_of_nonneg_right
    (show (9216 : ℝ) ≤ 10000 + 2 * rowDistanceTailConstant from by linarith)
    (Real.sqrt_nonneg (rowLogDegree d / rowLogComparisonQ n d (n - k)))
  have hBad := mul_le_mul_of_nonneg_right
    (show 2 * rowDistanceTailConstant ≤ 10000 + 2 * rowDistanceTailConstant from by linarith)
    (show 0 ≤ Real.sqrt (d : ℝ) * Real.log (rowReplacementUpperBound n η R / η) *
      Real.exp (-(1 / 262144) * rowLogComparisonQ n d (n - k)) from by positivity)
  change 9216 * Real.sqrt (rowLogDegree d / rowLogComparisonQ n d (n - k)) + _ ≤
    (10000 + 2 * rowDistanceTailConstant) * Real.sqrt (rowLogDegree d / rowLogComparisonQ n d (n - k)) + _
  nlinarith

/-- The full named proposition with the source row laws and independence
    assumptions on an arbitrary probability space. -/
def GeneralizedRowReplacementProposition : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (n d k : ℕ) (hd : 0 < d) (hdn : d ≤ n), 1 ≤ k → k < n →
    ∀ (η : ℝ), 0 < η → ∀ (u : Fin k → EuclideanSpace ℂ (Fin n)),
    1 ≤ rowLogComparisonQ n d (n - k) →
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (X : Fin k → Ω → RowSlice n d) (Y : Fin k → Ω → (Fin n → Bool)),
    (∀ i, Measurable (X i)) → (∀ i, Measurable (Y i)) →
    (∀ i, μ.map (X i) = rowSliceLaw n d) →
    (∀ i, μ.map (Y i) = bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
      (rowBernoulliParameter_le_one (show 0 < n by omega) hdn)) →
    iIndepFun X μ → iIndepFun Y μ →
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) μ →
    (1 / (n : ℝ)) *
      (∫ ω, |regularizedRowPotential (shiftedSliceRows u (fun i => X i ω)) η -
        regularizedRowPotential (shiftedBernoulliRows u (fun i => Y i ω)) η| ∂μ) ≤
      C * Real.sqrt (Real.log (Real.exp 1 * (d : ℝ)) / rowLogComparisonQ n d (n - k)) +
        C * Real.sqrt (d : ℝ) * Real.log (rowReplacementUpperBound n η (rowShiftNormBound u) / η) *
          Real.exp (-c * rowLogComparisonQ n d (n - k))

theorem generalized_row_replacement_proposition : GeneralizedRowReplacementProposition := by
  refine ⟨10000 + 2 * rowDistanceTailConstant, 1 / 262144, ?_, by norm_num, ?_⟩
  · dsimp [rowDistanceTailConstant]
    positivity
  · intro n d k hd hdn hk hkn η hη u hQ Ω _ μ hμ X Y hX hY hXlaw hYlaw hXind hYind hMutual
    letI := hμ
    exact (row_replacement_expected_bound hd hdn hk hkn hη u hQ μ X Y hX hY hXlaw hYlaw
      hXind hYind hMutual).trans (rowReplacementErrorBound_le_common n d k hη (rowShiftNormBound u))

end CircularLaw
