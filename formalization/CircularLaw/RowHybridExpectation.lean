import CircularLaw.RowHybrid
import CircularLaw.FiniteProductConditioning

/-!
# Conditional hybrid increments under the actual row laws

The comparison matrix may depend on every other row. Splitting the
product law fixes those rows and leaves the selected slice/Bernoulli pair
with its literal marginal laws. Integrating the uniform one-row estimate
therefore bounds each actual hybrid increment.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

def replacementRowPairLaw {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    Measure (ReplacementRowPair n d) :=
  (rowSliceLaw n d).prod (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
    (rowBernoulliParameter_le_one hn hdn))

instance replacementRowPairLaw_probability {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    IsProbabilityMeasure (replacementRowPairLaw hn hdn) := by
  haveI := rowSliceLaw_probability hdn
  unfold replacementRowPairLaw
  infer_instance

theorem replacementRowPairLaw_slice_marginal {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    (replacementRowPairLaw hn hdn).map Prod.fst = rowSliceLaw n d := by
  rw [replacementRowPairLaw, Measure.map_fst_prod]
  simp

theorem replacementRowPairLaw_bernoulli_marginal {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    (replacementRowPairLaw hn hdn).map Prod.snd =
      bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d) (rowBernoulliParameter_le_one hn hdn) := by
  haveI := rowSliceLaw_probability hdn
  rw [replacementRowPairLaw, Measure.map_snd_prod]
  simp

def rowReplacementErrorBound (n d k : ℕ) (η R : ℝ) : ℝ :=
  9216 * Real.sqrt (rowLogDegree d / rowLogComparisonQ n d (n - k)) +
    (2 * rowDistanceTailConstant) * Real.sqrt (d : ℝ) *
      Real.log (rowReplacementUpperBound n η R / η) *
        Real.exp (-(1 / 262144) * rowLogComparisonQ n d (n - k))

theorem rowReplacementUpperBound_ge_regularization (n : ℕ) {η : ℝ} (hη : 0 < η) (R : ℝ) :
    η ≤ rowReplacementUpperBound n η R := by
  calc
    η = Real.sqrt (η ^ 2) := (Real.sqrt_sq hη.le).symm
    _ ≤ Real.sqrt (η ^ 2 + (Real.sqrt (n : ℝ) + R) ^ 2) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

theorem rowReplacementErrorBound_nonneg (n d k : ℕ) {η : ℝ} (hη : 0 < η) (R : ℝ) :
    0 ≤ rowReplacementErrorBound n d k η R := by
  have hLog : 0 ≤ Real.log (rowReplacementUpperBound n η R / η) :=
    Real.log_nonneg ((one_le_div hη).mpr (rowReplacementUpperBound_ge_regularization n hη R))
  dsimp [rowReplacementErrorBound, rowDistanceTailConstant]
  positivity

theorem rowHybrid_coordinate_integral_le {m n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (hkn : m + 1 < n) {η : ℝ} (hη : 0 < η)
    (u : Fin (m + 1) → EuclideanSpace ℂ (Fin n))
    (hQ : 1 ≤ rowLogComparisonQ n d (n - (m + 1))) (i : Fin (m + 1))
    (rest : Fin m → ReplacementRowPair n d) :
    (∫ pair, |regularizedRowPotential (rowHybridMatrix u (i.val + 1) (i.insertNth pair rest)) η -
      regularizedRowPotential (rowHybridMatrix u i.val (i.insertNth pair rest)) η|
      ∂replacementRowPairLaw (by omega) hdn) ≤
      rowReplacementErrorBound n d (m + 1) η (rowShiftNormBound u) := by
  simp_rw [rowHybrid_potential_increment]
  exact hybrid_one_row_expected_increment hd hdn (by omega) hkn (hybridOtherRows u i rest) hη
    (u i) (norm_le_rowShiftNormBound u i) hQ (replacementRowPairLaw (by omega) hdn)
    Prod.fst measurable_fst (replacementRowPairLaw_slice_marginal _ _)
    Prod.snd measurable_snd (replacementRowPairLaw_bernoulli_marginal _ _)

theorem rowHybrid_expected_increment_le {m n d : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (hkn : m + 1 < n) {η : ℝ} (hη : 0 < η)
    (u : Fin (m + 1) → EuclideanSpace ℂ (Fin n))
    (hQ : 1 ≤ rowLogComparisonQ n d (n - (m + 1))) (i : Fin (m + 1)) :
    (∫ rows, |regularizedRowPotential (rowHybridMatrix u (i.val + 1) rows) η -
      regularizedRowPotential (rowHybridMatrix u i.val rows) η|
      ∂Measure.pi (fun _ : Fin (m + 1) => replacementRowPairLaw (by omega) hdn)) ≤
      rowReplacementErrorBound n d (m + 1) η (rowShiftNormBound u) := by
  apply finite_product_integral_le_of_coordinate_bound
  exact rowHybrid_coordinate_integral_le hd hdn hkn hη u hQ i

end CircularLaw
