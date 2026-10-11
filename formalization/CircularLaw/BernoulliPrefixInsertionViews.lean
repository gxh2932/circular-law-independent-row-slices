import CircularLaw.BernoulliPrefixFiltration
import CircularLaw.LastIndexDegreeNormalizedSteps
import CircularLaw.BernoulliUniqueRowLaw
import CircularLaw.UniqueNeighbourhoodGeometry

/-!
# The actual shifted Bernoulli insertion views

Deleting the last column of a shifted one-column rectangle gives the
shifted square. Deleting the last row of the next shifted square gives
that rectangle. The fresh column has no diagonal shift; the fresh row
has the shift in its last coordinate. These identities use the actual
ambient sample entries and the original raw shift.
-/

noncomputable section
open Classical
open scoped Matrix

namespace CircularLaw

def bernoulliShiftedSquarePrefix {m : ℕ} (u : Fin m × Fin m → Bool) (z : ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  diagonalEmbeddedShift (bernoulliRectangularMatrix u) (Function.Embedding.refl _) z

def bernoulliShiftedColumnPrefix {m : ℕ} (u : Fin m × Fin (m + 1) → Bool) (z : ℂ) :
    Matrix (Fin m) (Fin (m + 1)) ℂ :=
  diagonalEmbeddedShift (bernoulliRectangularMatrix u) Fin.castSuccEmb z

def sourceLastDiagonalRowShift (m : ℕ) (z : ℂ) : EuclideanSpace ℂ (Fin (m + 1)) :=
  WithLp.toLp 2 (fun j => if j = Fin.last m then -z else 0)

theorem bernoulli_shifted_column_prefix_old {m : ℕ}
    (u : Fin m × Fin (m + 1) → Bool) (z : ℂ) :
    (bernoulliShiftedColumnPrefix u z).submatrix id Fin.castSucc =
      bernoulliShiftedSquarePrefix (fun ij => u (ij.1, ij.2.castSucc)) z := by
  ext i j
  simp [bernoulliShiftedColumnPrefix, bernoulliShiftedSquarePrefix,
    diagonalEmbeddedShift, bernoulliRectangularMatrix]

theorem bernoulli_shifted_square_prefix_old {m : ℕ}
    (u : Fin (m + 1) × Fin (m + 1) → Bool) (z : ℂ) :
    (bernoulliShiftedSquarePrefix u z).submatrix Fin.castSucc id =
      bernoulliShiftedColumnPrefix (fun ij => u (ij.1.castSucc, ij.2)) z := by
  ext i j
  simp [bernoulliShiftedColumnPrefix, bernoulliShiftedSquarePrefix,
    diagonalEmbeddedShift, bernoulliRectangularMatrix]

theorem bernoulli_shifted_column_prefix_last {m : ℕ}
    (u : Fin m × Fin (m + 1) → Bool) (z : ℂ) :
    lastColumnVector (bernoulliShiftedColumnPrefix u z) =
      bernoulliCubeVector (fun i => u (i, Fin.last m)) := by
  ext i
  simp [lastColumnVector, bernoulliShiftedColumnPrefix,
    diagonalEmbeddedShift, bernoulliRectangularMatrix, bernoulliCubeVector]

theorem bernoulli_shifted_square_prefix_last {m : ℕ}
    (u : Fin (m + 1) × Fin (m + 1) → Bool) (z : ℂ) :
    lastRowVector (bernoulliShiftedSquarePrefix u z) =
      bernoulliCubeVector (fun j => u (Fin.last m, j)) + sourceLastDiagonalRowShift m z := by
  ext j
  simp only [lastRowVector, bernoulliShiftedSquarePrefix, diagonalEmbeddedShift,
    bernoulliRectangularMatrix, bernoulliCubeVector, sourceLastDiagonalRowShift,
    PiLp.add_apply, Function.Embedding.refl_apply]
  by_cases h : j = Fin.last m
  · simp [h, sub_eq_add_neg]
  · simp [h, Ne.symm h]

theorem bernoulli_shifted_square_prefix_adjoint {m : ℕ}
    (u : Fin m × Fin m → Bool) (z : ℂ) :
    (bernoulliShiftedSquarePrefix u z).conjTranspose =
      diagonalEmbeddedShift (bernoulliRectangularMatrix u).conjTranspose
        (Function.Embedding.refl _) (star z) := by
  ext i j
  by_cases h : i = j
  simp [bernoulliShiftedSquarePrefix, diagonalEmbeddedShift, Matrix.conjTranspose_apply,
    star_sub, h]
  simp [bernoulliShiftedSquarePrefix, diagonalEmbeddedShift, Matrix.conjTranspose_apply,
    eq_comm, h]

theorem bernoulli_ambient_column_prefix_old {N m : ℕ}
    (hm : m ≤ N) (hNext : m + 1 ≤ N) (x : BernoulliSquareSample N) (z : ℂ) :
    (bernoulliShiftedColumnPrefix (bernoulliPrefixSample hm hNext x) z).submatrix id Fin.castSucc =
      bernoulliShiftedSquarePrefix (bernoulliPrefixSample hm hm x) z :=
  bernoulli_shifted_column_prefix_old _ z

theorem bernoulli_ambient_row_prefix_old {N m : ℕ}
    (hm : m ≤ N) (hNext : m + 1 ≤ N) (x : BernoulliSquareSample N) (z : ℂ) :
    (bernoulliShiftedSquarePrefix (bernoulliPrefixSample hNext hNext x) z).submatrix Fin.castSucc id =
      bernoulliShiftedColumnPrefix (bernoulliPrefixSample hm hNext x) z :=
  bernoulli_shifted_square_prefix_old _ z

theorem bernoulli_ambient_column_prefix_fresh {N m : ℕ}
    (hm : m ≤ N) (hNext : m + 1 ≤ N) (x : BernoulliSquareSample N) (z : ℂ) :
    lastColumnVector (bernoulliShiftedColumnPrefix (bernoulliPrefixSample hm hNext x) z) =
      bernoulliCubeVector (fun i => x (bernoulliFreshColumnEntryEmbedding hm hNext i)) :=
  bernoulli_shifted_column_prefix_last _ z

theorem bernoulli_ambient_row_prefix_fresh {N m : ℕ}
    (hNext : m + 1 ≤ N) (x : BernoulliSquareSample N) (z : ℂ) :
    lastRowVector (bernoulliShiftedSquarePrefix (bernoulliPrefixSample hNext hNext x) z) =
      bernoulliCubeVector (fun j => x (bernoulliFreshRowEntryEmbedding hNext hNext j)) +
        sourceLastDiagonalRowShift m z :=
  bernoulli_shifted_square_prefix_last _ z

end CircularLaw
