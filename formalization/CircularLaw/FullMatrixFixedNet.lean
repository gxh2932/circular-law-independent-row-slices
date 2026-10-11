import CircularLaw.FixedNetSlice
import CircularLaw.FiniteProductFibers
import CircularLaw.EqualBlock

/-!
# Fixed-net estimates on the original full matrix law

An arbitrary deterministic retained set uses the exact marginal of the
full independent row-slice matrix. Reindexing the retained coordinates
preserves the Euclidean norm. The resulting estimate includes every
deterministic vector shift, including the empty retained set.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def indexedSliceMatrixVectorL2Norm {n d : ℕ} {ι : Type*} [Fintype ι]
    (rows : ι → RowSlice n d) (y : Fin n → ℂ) (V : ι → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 (fun i => rowLinearForm (rows i) y + V i) : EuclideanSpace ℂ ι)‖

theorem indexedSliceMatrixVectorL2Norm_fin {n d K : ℕ} (rows : Fin K → RowSlice n d)
    (y : Fin n → ℂ) (V : Fin K → ℂ) :
    indexedSliceMatrixVectorL2Norm rows y V = matrixVectorL2Norm (sliceRectangularMatrix rows) y V := rfl

theorem indexedSliceMatrixVectorL2Norm_reindex {n d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (rows : κ → RowSlice n d) (y : Fin n → ℂ) (V : κ → ℂ) :
    indexedSliceMatrixVectorL2Norm (fun i => rows (e i)) y (fun i => V (e i)) =
      indexedSliceMatrixVectorL2Norm rows y V := by
  have hSq : indexedSliceMatrixVectorL2Norm (fun i => rows (e i)) y (fun i => V (e i)) ^ 2 =
      indexedSliceMatrixVectorL2Norm rows y V ^ 2 := by
    simp only [indexedSliceMatrixVectorL2Norm, EuclideanSpace.norm_sq_eq]
    exact e.sum_comp (fun i => ‖rowLinearForm (rows i) y + V i‖ ^ 2)
  have hLeft : 0 ≤ indexedSliceMatrixVectorL2Norm (fun i => rows (e i)) y (fun i => V (e i)) := norm_nonneg _
  have hRight : 0 ≤ indexedSliceMatrixVectorL2Norm rows y V := norm_nonneg _
  nlinarith only [hSq, hLeft, hRight]

theorem indexedSliceMatrixVectorL2Norm_retained_matrix {n d : ℕ}
    (I : Finset (Fin n)) (rows : RowSliceMatrix n d) (y : Fin n → ℂ) (V : I → ℂ) :
    indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y V =
      ‖(WithLp.toLp 2 (fun i => (retainedShiftedMatrix I 0 rows).mulVec y i + V i) :
        EuclideanSpace ℂ I)‖ := by
  have hAction : (fun i : I => (retainedShiftedMatrix I 0 rows).mulVec y i + V i) =
      fun i : I => rowLinearForm (rows i.val) y + V i := by
    funext i
    simp only [retainedShiftedMatrix_mulVec, zero_mul, sub_zero]
  rw [hAction]
  rfl

theorem full_matrix_retained_probability_bound {n d : ℕ} (hdn : d ≤ n)
    (I : Finset (Fin n)) (y : Fin n → ℂ) (V : I → ℂ) {r P : ℝ}
    (hBound : ∀ W : Fin I.card → ℂ,
      uniformProbability (fun rows : Fin I.card → RowSlice n d =>
        matrixVectorL2Norm (sliceRectangularMatrix rows) y W ≤ r) ≤ P) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y V ≤ r) ≤ P := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty hdn
  rw [uniformProbability_pi_restrict (α := fun _ : Fin n => RowSlice n d) I
    (fun rows : I → RowSlice n d => indexedSliceMatrixVectorL2Norm rows y V ≤ r)]
  let e : I ≃ Fin I.card := Fintype.equivFinOfCardEq (by simp)
  let eRows : (I → RowSlice n d) ≃ (Fin I.card → RowSlice n d) :=
    { toFun := fun rows i => rows (e.symm i)
      invFun := fun rows i => rows (e i)
      left_inv := fun rows => by funext i; simp only [Equiv.symm_apply_apply]
      right_inv := fun rows => by funext i; simp only [Equiv.apply_symm_apply] }
  have h := hBound (fun i => V (e.symm i))
  rw [← uniformProbability_reindex eRows (fun rows : Fin I.card → RowSlice n d =>
    matrixVectorL2Norm (sliceRectangularMatrix rows) y (fun i => V (e.symm i)) ≤ r)] at h
  apply (uniformProbability_mono ?_).trans h
  intro rows hEvent
  change matrixVectorL2Norm (sliceRectangularMatrix (fun i => rows (e.symm i))) y
    (fun i => V (e.symm i)) ≤ r
  rw [← indexedSliceMatrixVectorL2Norm_fin, indexedSliceMatrixVectorL2Norm_reindex]
  exact hEvent

theorem eventually_full_matrix_fixed_net_estimate_uniform {Clower : ℝ} (hC : 96 ≤ Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ k : ℕ, 0 < k → ∀ I : Finset (Fin n),
        ∀ y : Fin n → ℂ, IsKVector k y → ∀ R : ℝ, 1 ≤ R → ∀ V : I → ℂ,
          uniformProbability (fun rows : RowSliceMatrix n d =>
            indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y V ≤
              R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤ fixedNetSliceEstimate k d I.card y R := by
  have hCPos : 0 < Clower := by linarith
  filter_upwards [eventually_fixed_net_slice_estimate_uniform hC σ,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ)] with n hFixed hConditions
  intro d hBand k hk I y hy R hR V
  by_cases hI : 0 < I.card
  · have hFinite := source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)
    apply full_matrix_retained_probability_bound (by omega) I y V
    intro W
    have hCount : I.card ≤ n := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_le_card (Finset.subset_univ I))
    exact hFixed d hBand k hk I.card hI hCount y hy R hR W
  · have hZero : I.card = 0 := by omega
    simpa [fixedNetSliceEstimate, hZero] using uniformProbability_le_one (fun rows : RowSliceMatrix n d =>
      indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y V ≤
        R * Real.log d * Real.sqrt ((d : ℝ) * n) / k)

end CircularLaw
