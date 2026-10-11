import CircularLaw.BernoulliProjectionSmallBall
import CircularLaw.ColumnAdditionLogIncrement

/-!
# Actual Bernoulli failure probabilities for the logarithmic exposure step

The probability estimate uses the actual leading-row kernel and actual
inserted singular-value log sum. A coordinate-spread basis and compatible
radius give the bound for row and column insertion. These geometric inputs
are explicit; the graph argument that supplies them is still separate.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

theorem row_adjoint_bernoulli_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) (u : EuclideanSpace ℂ ι) :
    rowAdjointVector (bernoulliCubeVector x + u) = bernoulliCubeVector x + rowAdjointVector u := by
  ext i
  simp only [row_adjoint_vector_apply, PiLp.add_apply, star_add]
  cases hxi : x i <;> simp [bernoulliCubeVector, hxi]

theorem bernoulli_projection_norm_small_ball_of_uniform_spread
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (B : OrthonormalBasis κ ℂ V)
    (hκ : 0 < Fintype.card κ) (u : EuclideanSpace ℂ ι) (S : κ → Finset ι)
    (hS : ∀ j, (S j).Nonempty) {k : ℕ} (hk : 0 < k) (hCard : ∀ j, k ≤ (S j).card)
    {ρ t R : ℝ} (hρ : 0 < ρ) (hR : 0 ≤ R)
    (hLarge : ∀ j, ∀ i ∈ S j, ρ ≤ ‖(B j : EuclideanSpace ℂ ι) i‖) (ht : ρ / 2 ≤ t)
    (hRadius : R ^ 2 ≤ (Fintype.card κ : ℝ) * t ^ 2 / 2) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ < R} ≤
      2 * bernoulliScalarSmallBallConstant * (t / ρ) / Real.sqrt ((k : ℝ) * p) := by
  have hContainment :
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ < R} ⊆
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ ^ 2 ≤
        (Fintype.card κ : ℝ) * t ^ 2 / 2} := by
    intro x hx
    have hNorm := norm_nonneg (V.starProjection (bernoulliCubeVector x + u))
    change ‖V.starProjection (bernoulliCubeVector x + u)‖ < R at hx
    change ‖V.starProjection (bernoulliCubeVector x + u)‖ ^ 2 ≤ _
    exact (sq_le_sq₀ hNorm hR |>.mpr hx.le).trans hRadius
  exact (measureReal_mono (h₂ := by finiteness) hContainment).trans
    (bernoulli_projection_small_ball_of_uniform_spread p hp hpPos hHalf V B hκ u S hS
      hk hCard hρ hLarge ht)

theorem bernoulli_row_log_failure_of_basis_spread
    {κ : Type*} [Fintype κ] {r n m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin n) (Fin m) ℂ) (h : r ≤ n)
    (hOld : 0 < leadingRowSingularProduct A h)
    (B : OrthonormalBasis κ ℂ (LinearMap.ker (leadingCompressedRows A h).toEuclideanLin))
    (hκ : 0 < Fintype.card κ) (u : EuclideanSpace ℂ (Fin m)) (S : κ → Finset (Fin m))
    (hS : ∀ j, (S j).Nonempty) {k : ℕ} (hk : 0 < k) (hCard : ∀ j, k ≤ (S j).card)
    {ρ t N δ : ℝ} (hρ : 0 < ρ) (hN : 0 < N)
    (hLarge : ∀ j, ∀ i ∈ S j, ρ ≤ ‖(B j : EuclideanSpace ℂ (Fin m)) i‖)
    (ht : ρ / 2 ≤ t)
    (hRadius : Real.exp (-N * δ) ^ 2 ≤ (Fintype.card κ : ℝ) * t ^ 2 / 2) :
    (bernoulliCubeLaw (Fin m) p hp).real
      {x | leadingRowLogPrefix A h / N + δ <
        insertedLeadingLogPrefix A h (bernoulliCubeVector x + u) / N} ≤
      2 * bernoulliScalarSmallBallConstant * (t / ρ) / Real.sqrt ((k : ℝ) * p) := by
  have hFailure := row_addition_log_failure_probability_le_projection_small
    (bernoulliCubeLaw (Fin m) p hp) A h (fun x => bernoulliCubeVector x + u) hOld (δ := δ) hN
  simp_rw [row_adjoint_bernoulli_shift] at hFailure
  exact hFailure.trans (bernoulli_projection_norm_small_ball_of_uniform_spread
    p hp hpPos hHalf _ B hκ (rowAdjointVector u) S hS hk hCard hρ
    (Real.exp_pos _).le hLarge ht hRadius)

theorem bernoulli_column_log_failure_of_basis_spread
    {κ : Type*} [Fintype κ] {r n m : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (A : Matrix (Fin n) (Fin m) ℂ) (hRow : r ≤ n) (hCol : r ≤ m) (hNext : r + 1 ≤ n)
    (hOld : 0 < leadingRowSingularProduct A hRow)
    (B : OrthonormalBasis κ ℂ (LinearMap.ker (leadingCompressedRows A.conjTranspose hCol).toEuclideanLin))
    (hκ : 0 < Fintype.card κ) (u : EuclideanSpace ℂ (Fin n)) (S : κ → Finset (Fin n))
    (hS : ∀ j, (S j).Nonempty) {k : ℕ} (hk : 0 < k) (hCard : ∀ j, k ≤ (S j).card)
    {ρ t N δ : ℝ} (hρ : 0 < ρ) (hN : 0 < N)
    (hLarge : ∀ j, ∀ i ∈ S j, ρ ≤ ‖(B j : EuclideanSpace ℂ (Fin n)) i‖)
    (ht : ρ / 2 ≤ t)
    (hRadius : Real.exp (-N * δ) ^ 2 ≤ (Fintype.card κ : ℝ) * t ^ 2 / 2) :
    (bernoulliCubeLaw (Fin n) p hp).real
      {x | leadingRowLogPrefix A hRow / N + δ <
        insertedColumnLeadingLogPrefix A hNext (bernoulliCubeVector x + u) / N} ≤
      2 * bernoulliScalarSmallBallConstant * (t / ρ) / Real.sqrt ((k : ℝ) * p) := by
  exact (column_addition_log_failure_probability_le_projection_small
    (bernoulliCubeLaw (Fin n) p hp) A hRow hCol hNext
    (fun x => bernoulliCubeVector x + u) hOld (δ := δ) hN).trans
      (bernoulli_projection_norm_small_ball_of_uniform_spread
        p hp hpPos hHalf _ B hκ u S hS hk hCard hρ
        (Real.exp_pos _).le hLarge ht hRadius)

end CircularLaw
