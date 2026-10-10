import CircularLaw.UniformRowsTensorization
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The matrix profile estimate and conditioning to row slices

The sampled matrix acts on the actual vector. Its norm is the Euclidean
norm on `EuclideanSpace`, and the exact slice-conditioning factor is applied
to the same matrix event.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def matrixVectorL2Norm {n K : ℕ} (M : Matrix (Fin K) (Fin n) ℂ)
    (y : Fin n → ℂ) (V : Fin K → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 (fun i => (M.mulVec y) i + V i) : EuclideanSpace ℂ (Fin K))‖

theorem matrixVectorL2Norm_sq {n K : ℕ} (M : Matrix (Fin K) (Fin n) ℂ)
    (y : Fin n → ℂ) (V : Fin K → ℂ) :
    matrixVectorL2Norm M y V ^ 2 = ∑ i, ‖(M.mulVec y) i + V i‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq _

theorem withReplacement_matrix_tensorization {n d K : ℕ} (hn : 0 < n)
    (y : Fin n → ℂ) {t A τ : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A) (hτ : 1 ≤ τ)
    (hsmall : ∀ σ, 1 ≤ σ → ∀ z : ℂ,
      uniformProbability (fun row : Fin d → Fin n => ‖(∑ i, y (row i)) - z‖ ≤ σ * t) ≤ A * σ ^ 2)
    (V : Fin K → ℂ) :
    uniformProbability (fun samples : OrderedRows n d K =>
      matrixVectorL2Norm (withReplacementMatrix samples) y V ≤ τ * t * Real.sqrt (K : ℝ)) ≤
        (4 * Real.exp 1 * A * τ ^ 2) ^ K := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := uniform_rows_tensorization (fun _ : Fin K => fun row : Fin d → Fin n => ∑ i, y (row i))
    ht hA hτ (fun _ => hsmall) (fun i => -V i)
  apply (uniformProbability_mono ?_).trans h
  intro samples hEvent
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hEvent 2
  change matrixVectorL2Norm (withReplacementMatrix samples) y V ^ 2 ≤ (τ * t * Real.sqrt (K : ℝ)) ^ 2 at hSq
  rw [matrixVectorL2Norm_sq, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg K)] at hSq
  simpa only [withReplacementMatrix_mulVec, sub_neg_eq_add] using hSq

theorem canonical_profile_matrix_tensorization {n k d K : ℕ}
    (hn : 0 < n) (hd : 65536 ≤ d) (hk : 0 < k) (y : Fin n → ℂ) (hy : IsKVector k y)
    (hrange : ∀ a b,
      |dyadicWeight (truncatedProfileWeight
        (canonicalRowProfile y ((d : ℝ) / (k : ℝ))) d
        ((canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part a)) -
       dyadicWeight (truncatedProfileWeight
        (canonicalRowProfile y ((d : ℝ) / (k : ℝ))) d
        ((canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part b))| ≤ (d : ℝ) / 12)
    (hdegree : Real.rpow (d : ℝ) (1 / 3 : ℝ) *
      Real.exp (-binomialHalfRate * Real.rpow (d : ℝ) (2 / 3 : ℝ)) ≤
        Real.exp (-(binomialHalfRate / 2) * Real.rpow (d : ℝ) (2 / 3 : ℝ)))
    {τ : ℝ} (hτ : 1 ≤ τ) (V : Fin K → ℂ) :
    let P := canonicalRowProfile y ((d : ℝ) / (k : ℝ))
    let A := 4 * Real.exp (-averagedProfileRate *
      pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) *
        profileGeometricMean P.part (truncatedProfileWeight P d) +
          Real.exp (-averagedProfileRate * Real.rpow (d : ℝ) (2 / 3 : ℝ))
    uniformProbability (fun samples : OrderedRows n d K =>
      matrixVectorL2Norm (withReplacementMatrix samples) y V ≤
        τ * Real.sqrt ((d : ℝ) * K) / (k : ℝ)) ≤
      (4 * Real.exp 1 * rowSmallBallConstant * τ ^ 2 * A) ^ K := by
  intro P A
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hW : 0 ≤ profileGeometricMean P.part (truncatedProfileWeight P d) := by
    rw [profileGeometricMean_eq_exp _ _ (truncatedProfileWeight_pos P (by omega))]
    exact Real.exp_nonneg _
  have hANonneg : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ rowSmallBallConstant := by linarith [rowSmallBallConstant_ge_one]
  have hkPos : (0 : ℝ) < k := by exact_mod_cast hk
  have hRadius : τ * (Real.sqrt (d : ℝ) / (k : ℝ)) * Real.sqrt (K : ℝ) =
      τ * Real.sqrt ((d : ℝ) * K) / (k : ℝ) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg d)]
    ring
  have h := withReplacement_matrix_tensorization hn y
    (t := Real.sqrt (d : ℝ) / (k : ℝ)) (A := rowSmallBallConstant * A)
    (by positivity) (mul_nonneg hC hANonneg) hτ (fun σ hσ z => by
      have h := canonical_averaged_row_small_ball hn hd hk y hy hrange hdegree hσ z 0
      have hRow : uniformProbability (fun row : Fin d → Fin n =>
          ‖(∑ i, y (row i)) - z‖ ≤ σ * (Real.sqrt (d : ℝ) / (k : ℝ))) ≤
          rowSmallBallConstant * σ ^ 2 * A := by
        simpa only [A, P, add_zero, mul_div_assoc] using h
      exact hRow.trans_eq (by ring)) V
  rw [hRadius] at h
  exact h.trans_eq (by congr 1; ring)

theorem canonical_profile_slice_tensorization {n k d K : ℕ}
    (hn : 0 < n) (hd : 65536 ≤ d) (hdn : 2 * d ≤ n) (hk : 0 < k)
    (y : Fin n → ℂ) (hy : IsKVector k y)
    (hrange : ∀ a b,
      |dyadicWeight (truncatedProfileWeight
        (canonicalRowProfile y ((d : ℝ) / (k : ℝ))) d
        ((canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part a)) -
       dyadicWeight (truncatedProfileWeight
        (canonicalRowProfile y ((d : ℝ) / (k : ℝ))) d
        ((canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part b))| ≤ (d : ℝ) / 12)
    (hdegree : Real.rpow (d : ℝ) (1 / 3 : ℝ) *
      Real.exp (-binomialHalfRate * Real.rpow (d : ℝ) (2 / 3 : ℝ)) ≤
        Real.exp (-(binomialHalfRate / 2) * Real.rpow (d : ℝ) (2 / 3 : ℝ)))
    {τ : ℝ} (hτ : 1 ≤ τ) (V : Fin K → ℂ) :
    let P := canonicalRowProfile y ((d : ℝ) / (k : ℝ))
    let A := 4 * Real.exp (-averagedProfileRate *
      pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) *
        profileGeometricMean P.part (truncatedProfileWeight P d) +
          Real.exp (-averagedProfileRate * Real.rpow (d : ℝ) (2 / 3 : ℝ))
    uniformProbability (fun rows : Fin K → RowSlice n d =>
      matrixVectorL2Norm (sliceRectangularMatrix rows) y V ≤
        τ * Real.sqrt ((d : ℝ) * K) / (k : ℝ)) ≤
      Real.exp (2 * K * (d : ℝ) ^ 2 / n) *
        (4 * Real.exp 1 * rowSmallBallConstant * τ ^ 2 * A) ^ K := by
  intro P A
  exact (condition_matrix_event_to_slice_exp hn hdn (fun M =>
    matrixVectorL2Norm M y V ≤ τ * Real.sqrt ((d : ℝ) * K) / (k : ℝ))).trans
      (mul_le_mul_of_nonneg_left
        (canonical_profile_matrix_tensorization hn hd hk y hy hrange hdegree hτ V)
        (Real.exp_nonneg _))

end CircularLaw
