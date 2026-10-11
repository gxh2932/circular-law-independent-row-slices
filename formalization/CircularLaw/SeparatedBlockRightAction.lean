import CircularLaw.SeparatedBlockSliceSmallBall
import CircularLaw.Tensorization
import CircularLaw.FullMatrixFixedNet
import CircularLaw.FiniteLawTransport

/-!
# Direct right-action bounds from large separated blocks

Independent exact rows tensorize the scalar separated-block estimate.
Every retained matrix uses its actual product marginal, and deterministic
shifts include the scalar corrections in the steep-vector nets.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CircularLaw

theorem row_slice_separated_blocks_right_action_squared_small_ball {n d K : ℕ}
    (hd : 0 < d) (hSize : 2 * d ≤ n) (L R : Finset (Fin n))
    (hLeft : L.Nonempty) (hR : 3 * (n : ℝ) / 4 ≤ R.card)
    (y : Fin n → ℂ) {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 1 ≤ τ)
    (hSep : ∀ l ∈ L, ∀ j ∈ R, ρ ≤ dist (y l) (y j)) (V : Fin K → ℂ) :
    uniformProbability (fun rows : Fin K → RowSlice n d =>
      (∑ i, ‖rowLinearForm (rows i) y + V i‖ ^ 2) ≤ τ ^ 2 * (ρ / 2) ^ 2 * K) ≤
      (4 * Real.exp 1 * separatedBlockSmallBallCoefficient (((d : ℝ) / n) * L.card) *
        τ ^ 2) ^ K := by
  letI : Nonempty (RowSlice n d) := rowSlice_nonempty (by omega : d ≤ n)
  let ν := finiteUniformMeasure (RowSlice n d)
  let μ := Measure.pi (fun _ : Fin K => ν)
  let f := fun S : RowSlice n d => rowLinearForm S y
  let A := separatedBlockSmallBallCoefficient (((d : ℝ) / n) * L.card)
  have hA : 0 ≤ A := separated_block_small_ball_coefficient_nonneg _
  rw [← finiteUniformMeasure_real, finiteUniformMeasure_pi]
  have h := tensorization_positive_radius μ (fun i rows => f (rows i))
    (fun _ => measurable_of_countable _)
    (iIndepFun_pi (fun _ => (measurable_of_countable f).aemeasurable))
    (by linarith : 0 < ρ / 2) hA hτ (by
      intro i σ hσ
      apply iSup_le
      intro z
      apply (ENNReal.le_ofReal_iff_toReal_le (by finiteness)
        (mul_nonneg hA (sq_nonneg σ))).mpr
      change μ.real {rows | ‖f (rows i) - z‖ ≤ σ * (ρ / 2)} ≤ A * σ ^ 2
      have hLaw := finite_law_event_real (measurable_pi_apply i)
        (measurePreserving_eval (fun _ : Fin K => ν) i).map_eq
        (fun S : RowSlice n d => ‖f S - z‖ ≤ σ * (ρ / 2))
      rw [hLaw, finiteUniformMeasure_real]
      exact row_slice_separated_blocks_small_ball_quadratic hd hSize L R hLeft hR y hρ
        hSep hσ z) (fun i => -V i)
  simpa only [f, A, sub_neg_eq_add] using h

theorem row_slice_separated_blocks_right_action_norm_small_ball {n d K : ℕ}
    (hd : 0 < d) (hSize : 2 * d ≤ n) (L R : Finset (Fin n))
    (hLeft : L.Nonempty) (hR : 3 * (n : ℝ) / 4 ≤ R.card)
    (hRows : (n : ℝ) / 2 ≤ K) (y : Fin n → ℂ)
    (hSep : ∀ l ∈ L, ∀ j ∈ R, (2 / 3 : ℝ) ≤ dist (y l) (y j)) (V : Fin K → ℂ) :
    uniformProbability (fun rows : Fin K → RowSlice n d =>
      matrixVectorL2Norm (sliceRectangularMatrix rows) y V ≤ Real.sqrt n / 3) ≤
      (8 * Real.exp 1 * separatedBlockSmallBallCoefficient (((d : ℝ) / n) * L.card)) ^ K := by
  have hτ : 1 ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h := row_slice_separated_blocks_right_action_squared_small_ball hd hSize L R
    hLeft hR y (by norm_num : (0 : ℝ) < 2 / 3) hτ hSep V
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hBase : 4 * Real.exp 1 * separatedBlockSmallBallCoefficient
      (((d : ℝ) / n) * L.card) * 2 = 8 * Real.exp 1 *
        separatedBlockSmallBallCoefficient (((d : ℝ) / n) * L.card) := by ring
  rw [hBase] at h
  apply (uniformProbability_mono ?_).trans h
  intro rows hSmall
  have hSquare := pow_le_pow_left₀ (norm_nonneg _) hSmall 2
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at hSquare
  change ‖(WithLp.toLp 2 (fun i => rowLinearForm (rows i) y + V i) :
    EuclideanSpace ℂ (Fin K))‖ ^ 2 ≤ _ at hSquare
  rw [EuclideanSpace.norm_sq_eq] at hSquare
  nlinarith only [hSquare, hRows]

theorem row_slice_retained_separated_blocks_right_action_norm_small_ball {n d : ℕ}
    (hd : 0 < d) (hSize : 2 * d ≤ n) (L R : Finset (Fin n))
    (hLeft : L.Nonempty) (hR : 3 * (n : ℝ) / 4 ≤ R.card)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card) (y : Fin n → ℂ) (c ζ : ℂ)
    (hSep : ∀ l ∈ L, ∀ j ∈ R, (2 / 3 : ℝ) ≤ dist (y l) (y j)) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin
        (WithLp.toLp 2 (fun j => y j + c))‖ ≤ Real.sqrt n / 3) ≤
      (8 * Real.exp 1 * separatedBlockSmallBallCoefficient (((d : ℝ) / n) * L.card)) ^ I.card := by
  have h := full_matrix_retained_probability_bound (by omega : d ≤ n) I y
    (fun i => (d : ℂ) * c - ζ * (y i.val + c))
    (fun V => row_slice_separated_blocks_right_action_norm_small_ball hd hSize L R
      hLeft hR hRows y hSep V)
  have hAction (rows : RowSliceMatrix n d) :
      (WithLp.toLp 2 (fun i : I => rowLinearForm (rows i.val) y +
        ((d : ℂ) * c - ζ * (y i.val + c))) : EuclideanSpace ℂ I) =
      (retainedShiftedMatrix I ζ rows).toEuclideanLin (WithLp.toLp 2 (fun j => y j + c)) := by
    ext i
    change _ = (retainedShiftedMatrix I ζ rows).mulVec (fun j => y j + c) i
    rw [retainedShiftedMatrix_mulVec, rowLinearForm_add_const]
    ring
  simpa only [indexedSliceMatrixVectorL2Norm, hAction] using h

end CircularLaw
