import CircularLaw.BernoulliSliceMassBound
import CircularLaw.MatrixEnergyShift

/-!
# The literal independent-entry Bernoulli square matrix

Samples have one independent Boolean for every ordered entry. The sparse
law uses `p = d/n` whenever the degree is valid. Its parameter is clipped
only to give a probability law at every early dimension of a sequence.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Matrix

namespace CircularLaw

abbrev BernoulliSquareSample (n : ℕ) := (Fin n × Fin n) → Bool

def bernoulliSquareMatrix {n : ℕ} (x : BernoulliSquareSample n) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => cond (x (i, j)) 1 0

def bernoulliSquareMatrixLaw (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    Measure (BernoulliSquareSample n) := bernoulliCubeLaw (Fin n × Fin n) p hp

instance bernoulliSquareMatrixLaw_probability (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernoulliSquareMatrixLaw n p hp) := by
  unfold bernoulliSquareMatrixLaw
  infer_instance

theorem bernoulliSquareMatrixLaw_entries_independent (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    iIndepFun (fun ij : Fin n × Fin n => fun x : BernoulliSquareSample n => x ij)
      (bernoulliSquareMatrixLaw n p hp) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

def bernoulliSquareCount {n : ℕ} (x : BernoulliSquareSample n) : ℝ :=
  ∑ i, ∑ j, (cond (x (i, j)) 1 0 : ℝ)

theorem bernoulliSquareMatrix_energy {n : ℕ} (x : BernoulliSquareSample n) :
    squareMatrixEnergy (bernoulliSquareMatrix x) = bernoulliSquareCount x := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  cases h : x (i, j) <;> simp [bernoulliSquareMatrix, h]

theorem bernoulliSquareCount_integral (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (∫ x, bernoulliSquareCount x ∂bernoulliSquareMatrixLaw n p hp) =
      (n : ℝ) * n * p := by
  have hInt (i j : Fin n) : Integrable
      (fun x : BernoulliSquareSample n => (cond (x (i, j)) 1 0 : ℝ))
      (bernoulliSquareMatrixLaw n p hp) :=
    Integrable.of_finite
  have hCoord (i j : Fin n) :
      (∫ x : BernoulliSquareSample n, (cond (x (i, j)) 1 0 : ℝ)
        ∂bernoulliSquareMatrixLaw n p hp) = (p : ℝ) := by
    rw [bernoulliSquareMatrixLaw,
      bernoulliCubeLaw_coordinate_integral p hp (i, j) (fun b => (cond b 1 0 : ℝ)),
      bernoulliCoordinateLaw_integral]
    simp
  unfold bernoulliSquareCount
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hInt i j))]
  simp only [integral_finset_sum _ (fun j _ => hInt _ j), hCoord,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

def sparseBernoulliMatrixLaw (n d : ℕ) : Measure (BernoulliSquareSample n) :=
  bernoulliSquareMatrixLaw n (min (rowBernoulliParameter n d) 1) (min_le_right _ _)

instance sparseBernoulliMatrixLaw_probability (n d : ℕ) :
    IsProbabilityMeasure (sparseBernoulliMatrixLaw n d) := by
  unfold sparseBernoulliMatrixLaw
  infer_instance

theorem sparseBernoulliMatrixLaw_eq {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    sparseBernoulliMatrixLaw n d = bernoulliSquareMatrixLaw n
      (rowBernoulliParameter n d) (rowBernoulliParameter_le_one hn hdn) := by
  simp only [sparseBernoulliMatrixLaw,
    min_eq_left (rowBernoulliParameter_le_one hn hdn)]

theorem sparseBernoulliSquareCount_integral {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    (∫ x, bernoulliSquareCount x ∂sparseBernoulliMatrixLaw n d) = (n : ℝ) * d := by
  rw [sparseBernoulliMatrixLaw_eq hn hdn, bernoulliSquareCount_integral,
    rowBernoulliParameter_coe]
  field_simp

def normalizedShiftedBernoulliMatrix {n : ℕ} (d : ℕ) (z : ℂ)
    (x : BernoulliSquareSample n) : Matrix (Fin n) (Fin n) ℂ :=
  (Real.sqrt (d : ℝ) : ℂ)⁻¹ • bernoulliSquareMatrix x - z • 1

def bernoulliSingularMeasure {n : ℕ} (d : ℕ) (z : ℂ)
    (x : BernoulliSquareSample n) : Measure ℝ≥0 :=
  squareSingularMeasure (normalizedShiftedBernoulliMatrix d z x)

theorem bernoulliSingularMeasure_probability {n : ℕ} (hn : 0 < n) (d : ℕ) (z : ℂ)
    (x : BernoulliSquareSample n) : IsProbabilityMeasure (bernoulliSingularMeasure d z x) :=
  squareSingularMeasure_probability hn _

end CircularLaw
