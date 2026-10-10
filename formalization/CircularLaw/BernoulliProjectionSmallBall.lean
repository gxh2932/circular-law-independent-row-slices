import CircularLaw.WeightedBernoulliSmallBall
import CircularLaw.BernoulliQuadraticMoment
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Bernoulli projection anti-concentration from coordinate spread

The squared norm of an actual orthogonal projection is the sum of its
orthonormal coordinates. A small projection forces at least half these
coordinates to be small. Integrating that count and applying the proved
scalar estimate gives a probability bound for the literal Bernoulli law.
Coordinate spread is explicit; existence of a suitable basis is separate.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

theorem orthogonal_projection_basis_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (B : OrthonormalBasis κ ℂ V)
    (v : EuclideanSpace ℂ ι) :
    ‖V.starProjection v‖ ^ 2 = ∑ j, ‖⟪(B j : EuclideanSpace ℂ ι), v⟫_ℂ‖ ^ 2 := by
  simpa only [Submodule.starProjection_apply, Submodule.coe_norm,
    Submodule.inner_orthogonalProjection_eq_of_mem_left] using
    (B.sum_sq_norm_inner_right (V.orthogonalProjection v)).symm

theorem finite_small_coordinates_half_count {κ : Type*} [Fintype κ]
    (a : κ → ℝ) {t : ℝ} (ht : 0 < t)
    (hEnergy : (∑ j, a j ^ 2) ≤ (Fintype.card κ : ℝ) * t ^ 2 / 2) :
    (Fintype.card κ : ℝ) / 2 ≤ ∑ j, if a j ≤ t then (1 : ℝ) else 0 := by
  have hTerm (j : κ) : t ^ 2 * (if a j ≤ t then (0 : ℝ) else 1) ≤ a j ^ 2 := by
    by_cases hj : a j ≤ t
    · simp only [if_pos hj, mul_zero]; positivity
    · simp only [if_neg hj, mul_one]
      have hLarge : t < a j := lt_of_not_ge hj
      nlinarith
  have hSum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hTerm j)
  have hBig : (∑ j, if a j ≤ t then (0 : ℝ) else 1) =
      (Fintype.card κ : ℝ) - ∑ j, if a j ≤ t then (1 : ℝ) else 0 := by
    calc
      _ = ∑ j, (1 - (if a j ≤ t then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> norm_num
      _ = _ := by rw [Finset.sum_sub_distrib]; simp
  rw [← Finset.mul_sum, hBig] at hSum
  have hSquare : 0 < t ^ 2 := sq_pos_of_pos ht
  nlinarith

theorem bernoulli_cube_inner_linear_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) (x : ι → Bool) :
    ⟪v, bernoulliCubeVector x⟫_ℂ = ∑ i, weightedBernoulliValue (star (v i)) (x i) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  cases hxi : x i <;> simp [bernoulliCubeVector, weightedBernoulliValue, hxi]

theorem bernoulli_cube_shifted_inner_small_ball {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (v u : EuclideanSpace ℂ ι) (S : Finset ι) (hS : S.Nonempty)
    {ρ t : ℝ} (hρ : 0 < ρ) (hLarge : ∀ i ∈ S, ρ ≤ ‖v i‖) (ht : ρ / 2 ≤ t) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖⟪v, bernoulliCubeVector x + u⟫_ℂ‖ ≤ t} ≤
      bernoulliScalarSmallBallConstant * (t / ρ) / Real.sqrt ((S.card : ℝ) * p) := by
  have hBound := bernoulli_cube_linear_form_small_ball p hp hpPos hHalf
    (fun i => star (v i)) S hS hρ (by simpa only [norm_star] using hLarge) ht (-⟪v, u⟫_ℂ)
  simpa only [inner_add_right, bernoulli_cube_inner_linear_form, sub_neg_eq_add] using hBound

theorem bernoulli_projection_small_probability_le_coordinates
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (p : ℝ≥0) (hp : p ≤ 1) (V : Submodule ℂ (EuclideanSpace ℂ ι))
    (B : OrthonormalBasis κ ℂ V) (hκ : 0 < Fintype.card κ)
    (u : EuclideanSpace ℂ ι) {t : ℝ} (ht : 0 < t) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ ^ 2 ≤
        (Fintype.card κ : ℝ) * t ^ 2 / 2} ≤
      (2 / (Fintype.card κ : ℝ)) * ∑ j, (bernoulliCubeLaw ι p hp).real
        {x | ‖⟪(B j : EuclideanSpace ℂ ι), bernoulliCubeVector x + u⟫_ℂ‖ ≤ t} := by
  let μ := bernoulliCubeLaw ι p hp
  let A := {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ ^ 2 ≤
    (Fintype.card κ : ℝ) * t ^ 2 / 2}
  let C := fun j => {x | ‖⟪(B j : EuclideanSpace ℂ ι), bernoulliCubeVector x + u⟫_ℂ‖ ≤ t}
  have hCard : 0 < (Fintype.card κ : ℝ) := by exact_mod_cast hκ
  have hPoint (x : ι → Bool) : A.indicator (fun _ => (1 : ℝ)) x ≤
      (2 / (Fintype.card κ : ℝ)) * ∑ j, (C j).indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ A
    · have hEnergy := hx
      change ‖V.starProjection (bernoulliCubeVector x + u)‖ ^ 2 ≤ _ at hEnergy
      rw [orthogonal_projection_basis_energy V B] at hEnergy
      have hCount := finite_small_coordinates_half_count
        (fun j => ‖⟪(B j : EuclideanSpace ℂ ι), bernoulliCubeVector x + u⟫_ℂ‖) ht hEnergy
      simp only [Set.indicator_of_mem hx, Set.indicator_apply, C, Set.mem_setOf_eq]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hCard).mpr
      nlinarith
    · rw [Set.indicator_of_notMem hx]
      apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro j _
      by_cases hc : x ∈ C j <;> simp [hc]
  have hInt := integral_mono (μ := μ) (Integrable.of_finite)
    (Integrable.of_finite) hPoint
  rw [integral_indicator_const (μ := μ) (1 : ℝ) (Set.to_countable A).measurableSet,
    smul_eq_mul, mul_one, integral_const_mul,
    integral_finset_sum _ (fun _ _ => Integrable.of_finite)] at hInt
  have hCoordinateIntegral (j : κ) :
      (∫ x, (C j).indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real (C j) := by
    rw [integral_indicator_const (μ := μ) (1 : ℝ) (Set.to_countable (C j)).measurableSet,
      smul_eq_mul, mul_one]
  simp_rw [hCoordinateIntegral] at hInt
  exact hInt

theorem bernoulli_projection_small_ball_of_basis_spread
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (B : OrthonormalBasis κ ℂ V)
    (hκ : 0 < Fintype.card κ) (u : EuclideanSpace ℂ ι) (S : κ → Finset ι)
    (hS : ∀ j, (S j).Nonempty) {ρ t : ℝ} (hρ : 0 < ρ)
    (hLarge : ∀ j, ∀ i ∈ S j, ρ ≤ ‖(B j : EuclideanSpace ℂ ι) i‖) (ht : ρ / 2 ≤ t) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ ^ 2 ≤
        (Fintype.card κ : ℝ) * t ^ 2 / 2} ≤
      (2 / (Fintype.card κ : ℝ)) * ∑ j,
        bernoulliScalarSmallBallConstant * (t / ρ) / Real.sqrt (((S j).card : ℝ) * p) := by
  have htPos : 0 < t := lt_of_lt_of_le (by positivity : 0 < ρ / 2) ht
  have hCoef : 0 ≤ 2 / (Fintype.card κ : ℝ) :=
    div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hTerm (j : κ) :
      (bernoulliCubeLaw ι p hp).real
        {x | ‖⟪(B j : EuclideanSpace ℂ ι), bernoulliCubeVector x + u⟫_ℂ‖ ≤ t} ≤
        bernoulliScalarSmallBallConstant * (t / ρ) /
          Real.sqrt (((S j).card : ℝ) * p) :=
    bernoulli_cube_shifted_inner_small_ball p hp hpPos hHalf
      (B j : EuclideanSpace ℂ ι) u (S j) (hS j) hρ (hLarge j) ht
  exact (bernoulli_projection_small_probability_le_coordinates p hp V B hκ u htPos).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hTerm j)) hCoef)

theorem bernoulli_projection_small_ball_of_uniform_spread
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    (V : Submodule ℂ (EuclideanSpace ℂ ι)) (B : OrthonormalBasis κ ℂ V)
    (hκ : 0 < Fintype.card κ) (u : EuclideanSpace ℂ ι) (S : κ → Finset ι)
    (hS : ∀ j, (S j).Nonempty) {k : ℕ} (hk : 0 < k) (hCard : ∀ j, k ≤ (S j).card)
    {ρ t : ℝ} (hρ : 0 < ρ)
    (hLarge : ∀ j, ∀ i ∈ S j, ρ ≤ ‖(B j : EuclideanSpace ℂ ι) i‖) (ht : ρ / 2 ≤ t) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ ^ 2 ≤
        (Fintype.card κ : ℝ) * t ^ 2 / 2} ≤
      2 * bernoulliScalarSmallBallConstant * (t / ρ) / Real.sqrt ((k : ℝ) * p) := by
  have hK : 0 < (k : ℝ) := by exact_mod_cast hk
  have hRoot : 0 < Real.sqrt ((k : ℝ) * p) := Real.sqrt_pos.mpr (mul_pos hK hpPos)
  have htNonneg : 0 ≤ t := (by positivity : 0 ≤ ρ / 2).trans ht
  have hNumerator : 0 ≤ bernoulliScalarSmallBallConstant * (t / ρ) := by
    exact mul_nonneg bernoulli_scalar_small_ball_constant_pos.le (div_nonneg htNonneg hρ.le)
  have hTerm (j : κ) :
      bernoulliScalarSmallBallConstant * (t / ρ) / Real.sqrt (((S j).card : ℝ) * p) ≤
      bernoulliScalarSmallBallConstant * (t / ρ) / Real.sqrt ((k : ℝ) * p) := by
    apply div_le_div_of_nonneg_left hNumerator hRoot
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hCard j) p.coe_nonneg
  have hBound := bernoulli_projection_small_ball_of_basis_spread
    p hp hpPos hHalf V B hκ u S hS hρ hLarge ht
  calc
    _ ≤ (2 / (Fintype.card κ : ℝ)) *
        ∑ _j : κ, bernoulliScalarSmallBallConstant * (t / ρ) / Real.sqrt ((k : ℝ) * p) :=
      hBound.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hTerm j))
        (div_nonneg (by norm_num) (Nat.cast_nonneg _)))
    _ = _ := by
      have hBasisCard : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hκ
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

end CircularLaw
