import CircularLaw.BernoulliRectangularRestrictionLaw
import CircularLaw.BernoulliSourceUniqueExpansionProbability

/-!
# Full source expansion for restrictions of the actual ambient matrix

The exposure-law estimates transfer through the exact coordinate
marginal, in both orientations. Each event concerns one specified
restriction; simultaneous bounds across the exposure schedule still
require summing these failures with the relevant seed sizes.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix NNReal

namespace CircularLaw

theorem bernoulli_restricted_square_source_unique_expansion_failure
    {N M k : ℕ} (hN : 0 < N) (hMN : M ≤ N) (hk : 0 < k)
    (hRows : 3 * (N : ℝ) / 4 ≤ M) (r c : Fin M ↪ Fin N)
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 1024 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x | ¬ MatrixUniqueExpansionBudget
      ((bernoulliSquareMatrix x).submatrix r c) (Function.Embedding.refl _) β N d k
        (sourceGraphTerminalScale N d)} ≤
      2 * Real.exp (-d * k / 16) + (N : ℝ) * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
  rw [bernoulli_rectangular_restriction_event_probability r c p hp
    (fun A => ¬ MatrixUniqueExpansionBudget A (Function.Embedding.refl _) β N d k
      (sourceGraphTerminalScale N d))]
  exact bernoulli_ambient_square_source_unique_expansion_failure hN hMN hk hRows p hp hHalf
    hDegree hd hβ hβOne

theorem bernoulli_adjoint_restricted_square_source_unique_expansion_failure
    {N M k : ℕ} (hN : 0 < N) (hMN : M ≤ N) (hk : 0 < k)
    (hRows : 3 * (N : ℝ) / 4 ≤ M) (r c : Fin M ↪ Fin N)
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 1024 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x | ¬ MatrixUniqueExpansionBudget
      ((bernoulliSquareMatrix x)ᴴ.submatrix r c) (Function.Embedding.refl _) β N d k
        (sourceGraphTerminalScale N d)} ≤
      2 * Real.exp (-d * k / 16) + (N : ℝ) * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
  rw [bernoulli_adjoint_rectangular_restriction_event_probability r c p hp
    (fun A => ¬ MatrixUniqueExpansionBudget A (Function.Embedding.refl _) β N d k
      (sourceGraphTerminalScale N d))]
  exact bernoulli_ambient_square_source_unique_expansion_failure hN hMN hk hRows p hp hHalf
    hDegree hd hβ hβOne

theorem bernoulli_restricted_rectangular_source_unique_expansion_failure
    {N M k : ℕ} (hN : 0 < N) (hCN : M + 1 ≤ N) (hk : 0 < k)
    (hRows : 3 * (N : ℝ) / 4 ≤ M) (r : Fin M ↪ Fin N) (c : Fin (M + 1) ↪ Fin N)
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 1024 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x | ¬ MatrixUniqueExpansionBudget
      ((bernoulliSquareMatrix x).submatrix r c) Fin.castSuccEmb β N d k
        (sourceGraphTerminalScale N d)} ≤
      4 * Real.exp (-d * k / 16) + (N : ℝ) * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
  rw [bernoulli_rectangular_restriction_event_probability r c p hp
    (fun A => ¬ MatrixUniqueExpansionBudget A Fin.castSuccEmb β N d k
      (sourceGraphTerminalScale N d))]
  exact bernoulli_ambient_rectangular_source_unique_expansion_failure hN hCN hk hRows p hp hHalf
    hDegree hd hβ hβOne

theorem bernoulli_adjoint_restricted_rectangular_source_unique_expansion_failure
    {N M k : ℕ} (hN : 0 < N) (hCN : M + 1 ≤ N) (hk : 0 < k)
    (hRows : 3 * (N : ℝ) / 4 ≤ M) (r : Fin M ↪ Fin N) (c : Fin (M + 1) ↪ Fin N)
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 1024 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x | ¬ MatrixUniqueExpansionBudget
      ((bernoulliSquareMatrix x)ᴴ.submatrix r c) Fin.castSuccEmb β N d k
        (sourceGraphTerminalScale N d)} ≤
      4 * Real.exp (-d * k / 16) + (N : ℝ) * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
  rw [bernoulli_adjoint_rectangular_restriction_event_probability r c p hp
    (fun A => ¬ MatrixUniqueExpansionBudget A Fin.castSuccEmb β N d k
      (sourceGraphTerminalScale N d))]
  exact bernoulli_ambient_rectangular_source_unique_expansion_failure hN hCN hk hRows p hp hHalf
    hDegree hd hβ hβOne

end CircularLaw
