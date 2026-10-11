import CircularLaw.BernoulliProjectionRadius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The large-dimension Bernoulli projection estimate

For d=n*p at least one and h at least n*d^(-1/4), the actual Bernoulli
projection probability at radius kappa*sqrt(d)*h^(3/2)*n^(-3/2) is bounded
by an absolute constant times kappa+d^(-1/4). Ambient coordinate spaces
of size at most n and arbitrary deterministic shifts are permitted.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def bernoulliLargeProjectionConstant : ℝ := 16384 * bernoulliScalarSmallBallConstant

theorem bernoulli_large_projection_constant_pos : 0 < bernoulliLargeProjectionConstant :=
  mul_pos (by norm_num) bernoulli_scalar_small_ball_constant_pos

theorem projection_three_halves_eq {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem large_projection_inverse_dimension {n : ℕ}
    {p h : ℝ} (hp : 0 ≤ p) (hd : 1 ≤ (n : ℝ) * p)
    (hLarge : (n : ℝ) * ((n : ℝ) * p) ^ (-1 / 4 : ℝ) ≤ h) :
    1 / Real.sqrt (h * p) ≤ ((n : ℝ) * p) ^ (-1 / 4 : ℝ) := by
  have hdPos : 0 < (n : ℝ) * p := lt_of_lt_of_le zero_lt_one hd
  have hEnergy : ((n : ℝ) * p) ^ (3 / 4 : ℝ) ≤ h * p := by
    calc
      _ = (((n : ℝ) * p) ^ (-1 / 4 : ℝ)) * ((n : ℝ) * p) := by
        rw [show (3 / 4 : ℝ) = (-1 / 4 : ℝ) + 1 by norm_num,
          Real.rpow_add hdPos, Real.rpow_one]
      _ = ((n : ℝ) * (((n : ℝ) * p) ^ (-1 / 4 : ℝ))) * p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLarge hp
  have hHalf : ((n : ℝ) * p) ^ (1 / 2 : ℝ) ≤ h * p :=
    (Real.rpow_le_rpow_of_exponent_le hd (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)).trans hEnergy
  have hRoot : ((n : ℝ) * p) ^ (1 / 4 : ℝ) ≤ Real.sqrt (h * p) := by
    have h := Real.sqrt_le_sqrt hHalf
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hdPos.le] at h
    norm_num only [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num] at h
    exact h
  rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring, Real.rpow_neg hdPos.le]
  simpa only [one_div] using
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hdPos (1 / 4)) hRoot

theorem large_projection_source_radius_eq {n : ℕ} (hn : 0 < n)
    {p h κ : ℝ} (hh : 0 < h) :
    κ * Real.sqrt ((n : ℝ) * p) * h ^ (3 / 2 : ℝ) * (n : ℝ) ^ (-3 / 2 : ℝ) =
      κ * Real.sqrt p * h * Real.sqrt h / n := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.sqrt_mul hnReal.le, projection_three_halves_eq hh,
    show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring, Real.rpow_neg hnReal.le,
    projection_three_halves_eq hnReal]
  have hRoot := Real.sqrt_pos.mpr hnReal
  field_simp

theorem bernoulli_large_subspace_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    {n : ℕ} (hn : 0 < n) (hAmbient : Fintype.card ι ≤ n)
    (hd : 1 ≤ (n : ℝ) * p) (V : Submodule ℂ (EuclideanSpace ℂ ι))
    (hLarge : (n : ℝ) * ((n : ℝ) * p) ^ (-1 / 4 : ℝ) ≤ (Module.finrank ℂ V : ℝ))
    (u : EuclideanSpace ℂ ι) {κ : ℝ} (hκ : 0 ≤ κ) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖V.starProjection (bernoulliCubeVector x + u)‖ <
        κ * Real.sqrt ((n : ℝ) * p) * (Module.finrank ℂ V : ℝ) ^ (3 / 2 : ℝ) *
          (n : ℝ) ^ (-3 / 2 : ℝ)} ≤
      bernoulliLargeProjectionConstant * (κ + ((n : ℝ) * p) ^ (-1 / 4 : ℝ)) := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdPos : 0 < (n : ℝ) * p := lt_of_lt_of_le zero_lt_one hd
  have hDimReal : 0 < (Module.finrank ℂ V : ℝ) :=
    (mul_pos hnReal (Real.rpow_pos_of_pos hdPos _)).trans_le hLarge
  have hDim : 0 < Module.finrank ℂ V := by exact_mod_cast hDimReal
  simp_rw [large_projection_source_radius_eq hn hDimReal]
  have hBound := bernoulli_projection_radius_bound_of_ambient_le p hp hpPos hHalf V hDim u hκ hn hAmbient
  exact hBound.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (large_projection_inverse_dimension p.coe_nonneg hd hLarge))
    bernoulli_large_projection_constant_pos.le)

theorem bernoulli_large_subspace_row_adjoint_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (hpPos : 0 < (p : ℝ)) (hHalf : (p : ℝ) ≤ 1 / 2)
    {n : ℕ} (hn : 0 < n) (hAmbient : Fintype.card ι ≤ n)
    (hd : 1 ≤ (n : ℝ) * p) (V : Submodule ℂ (EuclideanSpace ℂ ι))
    (hLarge : (n : ℝ) * ((n : ℝ) * p) ^ (-1 / 4 : ℝ) ≤ (Module.finrank ℂ V : ℝ))
    (u : EuclideanSpace ℂ ι) {κ : ℝ} (hκ : 0 ≤ κ) :
    (bernoulliCubeLaw ι p hp).real
      {x | ‖V.starProjection (rowAdjointVector (bernoulliCubeVector x + u))‖ <
        κ * Real.sqrt ((n : ℝ) * p) * (Module.finrank ℂ V : ℝ) ^ (3 / 2 : ℝ) *
          (n : ℝ) ^ (-3 / 2 : ℝ)} ≤
      bernoulliLargeProjectionConstant * (κ + ((n : ℝ) * p) ^ (-1 / 4 : ℝ)) := by
  simp_rw [row_adjoint_bernoulli_shift]
  exact bernoulli_large_subspace_projection p hp hpPos hHalf hn hAmbient hd V hLarge
    (rowAdjointVector u) hκ

def BernoulliLargeProjectionLemma : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (p : ℝ≥0) (hp : p ≤ 1),
    0 < (p : ℝ) → (p : ℝ) ≤ 1 / 2 → 0 < n → m ≤ n → 1 ≤ (n : ℝ) * p →
    ∀ V : Submodule ℂ (EuclideanSpace ℂ (Fin m)),
      (n : ℝ) * ((n : ℝ) * p) ^ (-1 / 4 : ℝ) ≤ (Module.finrank ℂ V : ℝ) →
      ∀ (u : EuclideanSpace ℂ (Fin m)) (κ : ℝ), 0 < κ →
        (bernoulliCubeLaw (Fin m) p hp).real
          {x | ‖V.starProjection (rowAdjointVector (bernoulliCubeVector x + u))‖ <
            κ * Real.sqrt ((n : ℝ) * p) * (Module.finrank ℂ V : ℝ) ^ (3 / 2 : ℝ) *
              (n : ℝ) ^ (-3 / 2 : ℝ)} ≤
          C * (κ + ((n : ℝ) * p) ^ (-1 / 4 : ℝ))

theorem bernoulli_large_projection_lemma : BernoulliLargeProjectionLemma := by
  refine ⟨bernoulliLargeProjectionConstant, bernoulli_large_projection_constant_pos, ?_⟩
  intro n m p hp hpPos hHalf hn hm hd V hLarge u κ hκ
  exact bernoulli_large_subspace_row_adjoint_projection p hp hpPos hHalf hn
    (by simpa only [Fintype.card_fin] using hm) hd V hLarge u hκ.le

end CircularLaw
