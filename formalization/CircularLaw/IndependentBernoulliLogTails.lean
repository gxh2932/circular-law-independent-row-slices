import CircularLaw.BernoulliHermitizationPositiveTail
import CircularLaw.IndependentSquareMinimumFailure

/-!
# The Bernoulli logarithmic tails on the paper's independent coupling

The actual second marginal transports the checked positive and negative
raw tail limits. Initial invalid degree dimensions are harmless because
the marginal identity is required only eventually.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory Filter
open scoped Matrix Topology

namespace CircularLaw

theorem independent_square_bernoulli_event_real {n d : ℕ} (hdn : d ≤ n)
    (event : BernoulliSquareSample n → Prop) :
    (independentSquareComparisonLaw n d).real {samples | event samples.2} =
      (sparseBernoulliMatrixLaw n d).real {x | event x} :=
  finite_law_event_real measurable_snd (independent_square_bernoulli_marginal hdn) event

theorem varying_bernoulli_probability_on_independent_coupling (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d)
    (f : ∀ n, BernoulliSquareSample n → ℝ) (a : ℝ)
    (hLimit : VaryingConvergesInProbability (fun n => sparseBernoulliMatrixLaw n (d n)) f a) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n samples => f n samples.2) a := by
  intro ε hε
  apply (hLimit ε hε).congr'
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd
  exact (independent_square_bernoulli_event_real hd.2 (fun x => ε < |f n x - a|)).symm

theorem independent_bernoulli_bottom_negative_log_converges (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ) (hz : z ≠ 0)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n samples => empiricalBottomNegativeLog
        (squareSingularValuesNNReal (bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1))
        (hermitizationDeletionCount n (d n) a)) 0 := by
  intro ε hε
  have hBern := (bernoulli_raw_bottom_negative_log_converges d hDegree hSparse z hz
    (fun n => hermitizationDeletionCount n (d n) a)
    (hermitization_deletion_fraction_tendsto_zero d hDegree hSparse ha haOne)) ε hε
  apply hBern.congr'
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd
  exact (independent_square_bernoulli_event_real hd.2 (fun x => ε < |empiricalBottomNegativeLog
    (squareSingularValuesNNReal (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1))
    (hermitizationDeletionCount n (d n) a) - 0|)).symm

theorem independent_bernoulli_top_positive_log_converges (d : ℕ → ℕ)
    (hDegree : Tendsto d atTop atTop) (hSparse : SparseDegrees d) (z : ℂ)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1) :
    VaryingConvergesInProbability (fun n => independentSquareComparisonLaw n (d n))
      (fun n samples => squareTopPositiveLog
        (bernoulliSquareMatrix samples.2 - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1)
        (hermitizationDeletionCount n (d n) a)) 0 := by
  intro ε hε
  have hBern := (bernoulli_raw_top_positive_log_converges d hDegree hSparse z ha haOne) ε hε
  apply hBern.congr'
  filter_upwards [eventually_valid_bernoulli_degrees hDegree hSparse] with n hd
  exact (independent_square_bernoulli_event_real hd.2 (fun x => ε < |squareTopPositiveLog
    (bernoulliSquareMatrix x - (z * (Real.sqrt (d n : ℝ) : ℂ)) • 1)
    (hermitizationDeletionCount n (d n) a) - 0|)).symm

end CircularLaw
