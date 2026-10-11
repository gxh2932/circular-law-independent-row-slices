import CircularLaw.LLYColumnWitnessProbability
import CircularLaw.RowSliceColumnThreeHalves
import CircularLaw.LLYFirstSteepAction
import CircularLaw.LLYAlmostAdjointReduction

/-!
# Actual adjoint invertibility for the first LLY steep class

Actual unique columns and the 3d/2 column-degree event give the same
proved first-jump norm threshold as for the retained right action.
Their probabilities use the original square row-slice law.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem lly_unique_column_jump_action {n d : ℕ} (rows : RowSliceMatrix n d)
    (J : Finset (Fin n)) (i j : Fin n) (hUnique : rowSliceColumnSupport rows j ∩ J = {i})
    (hjJ : j ∉ J) (x : EuclideanSpace ℂ (Fin n)) (ζ : ℂ) {a b : ℝ} (hb : 0 ≤ b)
    (hTail : ∀ q : Fin n, q ∉ J → ‖x q‖ ≤ b) (hTop : a ≤ ‖x i‖)
    (hJump : 6 * (d : ℝ) * b < a) (hSpectral : ‖ζ‖ ≤ (d : ℝ))
    (hColumn : rowSliceColumnCount rows j ≤ 3 * (d : ℝ) / 2) :
    a / 2 ≤ ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x j‖ := by
  let S : RowSlice n (rowSliceColumnSupport rows j).card := ⟨rowSliceColumnSupport rows j, rfl⟩
  have hLower := unique_witness_action_lower S J i j hUnique hjJ (fun q => x q) 0 (star ζ) hTail
  simp only [norm_zero, mul_zero, add_zero, norm_star] at hLower
  have hDegree : ((rowSliceColumnSupport rows j).card : ℝ) ≤ 3 * (d : ℝ) / 2 := by
    rw [rowSliceColumnSupport_card]
    exact hColumn
  have hCost : (((rowSliceColumnSupport rows j).card : ℝ) - 1 + ‖ζ‖) * b ≤ 3 * d * b := by
    have hCoeff : ((rowSliceColumnSupport rows j).card : ℝ) - 1 + ‖ζ‖ ≤ 3 * d := by
      nlinarith only [hDegree, hSpectral, Nat.cast_nonneg (α := ℝ) d]
    exact mul_le_mul_of_nonneg_right hCoeff hb
  have hNorm : a / 2 ≤ ‖shiftedRowAction S (fun q => x q) 0 (star ζ) j‖ := by
    nlinarith only [hLower, hTop, hJump, hCost]
  rw [shifted_slice_adjoint_apply_eq_column_sum]
  simpa only [shiftedRowAction, add_zero, rowLinearForm_eq_support_sum] using hNorm

theorem lly_unique_column_jump_norm {n d s t : ℕ} (hs : 0 < s) (hst : s ≤ t) (htn : t ≤ n)
    (rows : RowSliceMatrix n d) (hWitness : UniformUniqueColumnWitness s t rows)
    (hColumns : RowSliceColumnBound (3 * (d : ℝ) / 2) rows)
    (x : EuclideanSpace ℂ (Fin n)) (ζ : ℂ)
    (hJump : 6 * (d : ℝ) * orderedNormAt (fun j => x j) t < orderedNormAt (fun j => x j) s)
    (hSpectral : ‖ζ‖ ≤ (d : ℝ)) :
    Real.sqrt d / 4 * orderedNormAt (fun j => x j) s ≤
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ := by
  let L := orderedPrefix (fun j => x j) s
  let J := orderedPrefix (fun j => x j) t
  have hLJ : L ⊆ J := orderedPrefix_subset _ hst
  let G := rowSliceUniqueColumns L J rows \ J
  have hCard : (d : ℝ) * s / 2 ≤ G.card := hWitness L J hLJ
    (orderedPrefix_card _ (by omega : s ≤ n)) (orderedPrefix_card _ htn)
  let T := orderedNormAt (fun j => x j) s
  have hT : 0 ≤ T := orderedNormAt_nonneg _ _
  have hLarge : ∀ j ∈ G, T / 2 ≤ ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x j‖ := by
    intro j hj
    obtain ⟨i, hiL, hUnique⟩ := row_slice_unique_column_witness L J hLJ rows j (Finset.mem_sdiff.mp hj).1
    exact lly_unique_column_jump_action rows J i j hUnique (Finset.mem_sdiff.mp hj).2 x ζ
      (orderedNormAt_nonneg _ _) (fun q hq => norm_le_orderedNormAt_notMem_prefix _ (by omega : 0 < t) htn q hq)
      (orderedNormAt_le_norm_mem_prefix _ hs (by omega : s ≤ n) i hiL) hJump hSpectral (hColumns j)
  have hEnergy := euclidean_subset_coordinates_energy_lower G
    ((fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x)
    (div_nonneg (orderedNormAt_nonneg _ _) (by norm_num) : 0 ≤ T / 2) hLarge
  have hCountEnergy := mul_le_mul_of_nonneg_right hCard (sq_nonneg (T / 2))
  have hCoeff : (d : ℝ) / 16 ≤ (d : ℝ) * s / 8 := by
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have h := mul_le_mul_of_nonneg_left hsR (Nat.cast_nonneg (α := ℝ) d)
    nlinarith only [h, Nat.cast_nonneg (α := ℝ) d]
  apply (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt d / 4 * T) (norm_nonneg _)).mp
  calc
    _ = (d : ℝ) / 16 * T ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      ring
    _ ≤ (d : ℝ) * s / 8 * T ^ 2 := mul_le_mul_of_nonneg_right hCoeff (sq_nonneg T)
    _ = ((d : ℝ) * s / 2) * (T / 2) ^ 2 := by ring
    _ ≤ _ := hCountEnergy.trans hEnergy

theorem lly_first_steep_adjoint_norm {n d ℓ r k : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n) (rows : RowSliceMatrix n d)
    (hWitness : LLYFirstColumnWitness ℓ r k rows) (hColumns : RowSliceColumnBound (3 * (d : ℝ) / 2) rows)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) (x : EuclideanSpace ℂ (Fin n))
    (hUnit : ‖x‖ = 1) (hFirst : (fun j => x j) ∈ llyFirstSteep d ℓ r k) :
    Real.sqrt d / (4 * llyFirstSteepNormConstant n d r) ≤
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ := by
  obtain ⟨i, hi, hJump, hNorm⟩ := lly_first_jump_norm_bound hn hd hk x hFirst
  have hB := lly_first_steep_norm_constant_pos (r := r) hn hd
  rw [hUnit] at hNorm
  have hTop : 1 / llyFirstSteepNormConstant n d r ≤
      orderedNormAt (fun j => x j) (llyFirstRank ℓ k i) :=
    (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hNorm)
  have hAction := lly_unique_column_jump_norm (lly_first_rank_pos hℓ hk i)
    (lly_first_rank_mono hℓ (by omega : i ≤ i + 1))
    ((lly_first_rank_le ℓ k (i + 1)).trans hkn) rows (hWitness i hi) hColumns x ζ hJump hSpectral
  calc
    _ = Real.sqrt d / 4 * (1 / llyFirstSteepNormConstant n d r) := by ring
    _ ≤ Real.sqrt d / 4 * orderedNormAt (fun j => x j) (llyFirstRank ℓ k i) :=
      mul_le_mul_of_nonneg_left hTop (by positivity)
    _ ≤ _ := hAction

def llyFirstSteepAdjointFailure {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d)
    (ℓ r k : ℕ) (τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ (fun j => x j) ∈ llyFirstSteep d ℓ r k ∧
    ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ ≤ τ

theorem lly_first_steep_adjoint_failure_probability {n d ℓ r k : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n) (hℓ : 0 < ℓ) (hk : 0 < k) (hkn : k ≤ n)
    {ε : ℝ} (hε : 0 ≤ ε) (hSize : (d : ℝ) * k ≤ ε * n)
    (hBudget : 16 * (1 + Real.log (n : ℝ)) ≤ ε ^ 2 * d)
    (hError : ε * ℓ ≤ 1 / 8) (hStride : (ℓ : ℝ) ≤ (d : ℝ) / 4)
    (ζ : ℂ) (hSpectral : ‖ζ‖ ≤ (d : ℝ)) {τ : ℝ}
    (hThreshold : τ < Real.sqrt d / (4 * llyFirstSteepNormConstant n d r)) :
    uniformProbability (fun rows : RowSliceMatrix n d => llyFirstSteepAdjointFailure ζ rows ℓ r k τ) ≤
      (r + 1 : ℕ) * Real.exp (-ε ^ 2 * (d : ℝ) / 16) + (n : ℝ) * Real.exp (-2 * sliceTailRate * d) := by
  apply (uniformProbability_mono ?_).trans
    ((uniformProbability_or_le (fun rows : RowSliceMatrix n d => ¬LLYFirstColumnWitness ℓ r k rows)
      (fun rows : RowSliceMatrix n d => ¬RowSliceColumnBound (3 * (d : ℝ) / 2) rows)).trans ?_)
  · intro rows hFail
    by_contra hGood
    push_neg at hGood
    obtain ⟨x, hUnit, hFirst, hSmall⟩ := hFail
    have hNorm := lly_first_steep_adjoint_norm hn hd hℓ hk hkn rows hGood.1 hGood.2 ζ hSpectral x hUnit hFirst
    exact not_lt_of_ge (hNorm.trans hSmall) hThreshold
  · exact add_le_add (lly_first_column_witness_failure_probability hn hdn hℓ hk hkn hε hSize hBudget hError hStride)
      (square_rowSliceColumn_three_halves_failure hn hdn)

end CircularLaw
