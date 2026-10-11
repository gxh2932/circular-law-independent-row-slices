import CircularLaw.BernoulliExposureSmallSetCardinality
import CircularLaw.FiniteSmallSetExpansionUnion

/-!
# Uniform small-set expansion under the actual exposure laws

The square minor and the one-column rectangular matrix have at least
three quarters of the ambient rows. All small sets above the seed are
controlled at the original ambient degree, with explicit failure
probabilities 2*exp(-d*k/16) and 4*exp(-d*k/16), respectively.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem bernoulli_ambient_square_small_set_expansion_failure
    {N M k : ℕ} (hN : 0 < N) (hMN : M ≤ N) (hk : 0 < k)
    (hRows : 3 * (N : ℝ) / 4 ≤ M)
    (p : ℝ≥0) (hp : p ≤ 1) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 64 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw M p hp).real {x | ∃ S : Finset (Fin M), k ≤ S.card ∧
      (S.card : ℝ) * p ≤ 1 / 2 ∧
      ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x) (Function.Embedding.refl _) β S).card : ℝ) <
        sourceGraphExpansion N d S.card} ≤ 2 * Real.exp (-d * k / 16) := by
  simpa only [mul_one, one_mul] using small_set_cardinality_failure_to_uniform
    (bernoulliSquareMatrixLaw M p hp) hk p hd (by norm_num : (0 : ℝ) ≤ 1)
    (fun x S => ((matrixUniqueNeighbourhood (bernoulliSquareMatrix x)
      (Function.Embedding.refl _) β S).card : ℝ))
    (fun ell hell hSmall => by
      simpa only [one_mul] using
        bernoulli_ambient_square_small_cardinality_expansion_failure (ell := ell) hN hMN hell hRows p hp
          hDegree hd hSmall hβ hβOne)

theorem bernoulli_ambient_rectangular_small_set_expansion_failure
    {N M k : ℕ} (hN : 0 < N) (hMN : M ≤ N) (hk : 0 < k)
    (hRows : 3 * (N : ℝ) / 4 ≤ M)
    (p : ℝ≥0) (hp : p ≤ 1) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 64 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliCubeLaw (Fin M × Fin (M + 1)) p hp).real {x |
      ∃ S : Finset (Fin (M + 1)), k ≤ S.card ∧ (S.card : ℝ) * p ≤ 1 / 2 ∧
        ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) Fin.castSuccEmb β S).card : ℝ) <
          sourceGraphExpansion N d S.card} ≤ 4 * Real.exp (-d * k / 16) := by
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using small_set_cardinality_failure_to_uniform
    (bernoulliCubeLaw (Fin M × Fin (M + 1)) p hp) hk p hd (by norm_num : (0 : ℝ) ≤ 2)
    (fun x S => ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) Fin.castSuccEmb β S).card : ℝ))
    (fun ell hell hSmall => bernoulli_ambient_rectangular_small_cardinality_expansion_failure (ell := ell)
      hN hMN hell hRows p hp hDegree hd hSmall hβ hβOne)

end CircularLaw
