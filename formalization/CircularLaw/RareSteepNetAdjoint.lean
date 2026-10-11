import CircularLaw.RareRowSliceFullAdjoint
import CircularLaw.FiniteMean

/-!
# Fixed-vector and finite-net rare steep adjoint estimates

The norm threshold is proportional to sqrt(rank*d), rather than
sqrt(n). All probabilities concern the actual full shifted slice
adjoint, and the finite union charges both literal net cardinalities.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem row_slice_ordered_rare_adjoint_norm_decay {n d rank tail : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hRank : 0 < rank) (hRankTail : rank ≤ tail)
    (hFit : tail + rank ≤ n) (hRare : (rank : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (hCost : Real.log (4 * Real.exp 1 ^ 2 * Real.sqrt d) ≤ (d : ℝ) / 16)
    (y : Fin n → ℂ) (c ζ : ℂ)
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      (2 / 3 : ℝ) + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
        (WithLp.toLp 2 (fun i => y i + c))‖ ≤ Real.sqrt ((rank : ℝ) * d) / 30) ≤
      Real.exp (-(rank : ℝ) * d / 16) := by
  have hBound := row_slice_ordered_rare_adjoint_decay hd hDegree hRank hRankTail hFit hRare hCost
    y c ζ (by norm_num : (0 : ℝ) < 1 / 3) (by
      simpa only [show (2 : ℝ) * (1 / 3) = 2 / 3 by ring] using hGap)
  apply (uniformProbability_mono ?_).trans hBound
  intro rows hSmall
  have hSquare := pow_le_pow_left₀ (norm_nonneg _) hSmall 2
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ (rank : ℝ) * d)] at hSquare
  have hNonneg : 0 ≤ (rank : ℝ) * d := by positivity
  nlinarith

theorem rare_steep_net_adjoint_union_probability {n d rank tail : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hRank : 0 < rank) (hRankTail : rank ≤ tail)
    (hFit : tail + rank ≤ n) (hRare : (rank : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (hCost : Real.log (4 * Real.exp 1 ^ 2 * Real.sqrt d) ≤ (d : ℝ) / 16)
    (N : Finset (Fin n → ℂ))
    (hGap : ∀ u ∈ N, ∀ j : Fin n, tail ≤ j.val →
      (2 / 3 : ℝ) + orderedNorm u j < orderedNorm u ⟨rank - 1, by omega⟩)
    (C : Finset ℂ) (ζ : ℂ) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ∃ u ∈ N, ∃ w ∈ C,
        ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin
          (WithLp.toLp 2 (fun i => u i + w))‖ ≤ Real.sqrt ((rank : ℝ) * d) / 30) ≤
      (N.card : ℝ) * C.card * Real.exp (-(rank : ℝ) * d / 16) := by
  apply (uniformProbability_finset_exists_le N _).trans
  calc
    _ ≤ ∑ _u ∈ N, (C.card : ℝ) * Real.exp (-(rank : ℝ) * d / 16) := by
      apply Finset.sum_le_sum
      intro u hu
      apply (uniformProbability_finset_exists_le C _).trans
      calc
        _ ≤ ∑ _w ∈ C, Real.exp (-(rank : ℝ) * d / 16) :=
          Finset.sum_le_sum (fun w _ => row_slice_ordered_rare_adjoint_norm_decay
            hd hDegree hRank hRankTail hFit hRare hCost u w ζ (hGap u hu))
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end CircularLaw
