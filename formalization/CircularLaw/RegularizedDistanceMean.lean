import CircularLaw.BernoulliQuadraticMoment
import Mathlib.Probability.Moments.Variance

/-!
# The literal Bernoulli mean and regularized-distance scale

The second moment in Section 8 is the exact squared scale. Nonnegativity
of variance gives the mean upper bound without a concentration premise.
The cube norm bound also gives the deterministic upper bound used by the
hybrid argument, uniformly over every zero-one row.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal InnerProductSpace ComplexOrder MatrixOrder

namespace CircularLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def regularizedDistanceScale (P : Matrix ι ι ℂ) (η : ℝ)
    (u : EuclideanSpace ℂ ι) (p : ℝ≥0) : ℝ :=
  Real.sqrt (regularizedDistanceScaleSq P η u p)

def regularizedDistanceMean (P : Matrix ι ι ℂ) (η : ℝ)
    (u : EuclideanSpace ℂ ι) (p : ℝ≥0) (hp : p ≤ 1) : ℝ :=
  ∫ x : ι → Bool, regularizedDistance P η u (bernoulliCubeVector x)
    ∂bernoulliCubeLaw ι p hp

theorem regularizedDistanceScaleSq_nonneg {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (p : ℝ≥0) (hp : p ≤ 1) (η : ℝ) (u : EuclideanSpace ℂ ι) :
    0 ≤ regularizedDistanceScaleSq P η u p := by
  rw [← regularizedDistance_bernoulli_second_moment hP p hp η u]
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem regularizedDistanceScale_sq {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (p : ℝ≥0) (hp : p ≤ 1) (η : ℝ) (u : EuclideanSpace ℂ ι) :
    regularizedDistanceScale P η u p ^ 2 = regularizedDistanceScaleSq P η u p :=
  Real.sq_sqrt (regularizedDistanceScaleSq_nonneg hP p hp η u)

theorem regularizedDistanceMean_nonneg (P : Matrix ι ι ℂ)
    (p : ℝ≥0) (hp : p ≤ 1) (η : ℝ) (u : EuclideanSpace ℂ ι) :
    0 ≤ regularizedDistanceMean P η u p hp :=
  integral_nonneg (fun x => regularizedDistance_nonneg P η u (bernoulliCubeVector x))

theorem regularizedDistanceMean_ge_eta {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (p : ℝ≥0) (hp : p ≤ 1) (η : ℝ) (u : EuclideanSpace ℂ ι) :
    η ≤ regularizedDistanceMean P η u p hp := by
  have h := integral_mono (μ := bernoulliCubeLaw ι p hp)
    (f := fun _ => η) (g := fun x => regularizedDistance P η u (bernoulliCubeVector x))
    Integrable.of_finite Integrable.of_finite
    (fun x => regularizedDistance_ge_eta hP η u (bernoulliCubeVector x))
  simpa only [integral_const, probReal_univ, one_smul, regularizedDistanceMean] using h

theorem regularizedDistanceMean_le_scale {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (p : ℝ≥0) (hp : p ≤ 1) (η : ℝ) (u : EuclideanSpace ℂ ι) :
    regularizedDistanceMean P η u p hp ≤ regularizedDistanceScale P η u p := by
  have hVariance := variance_nonneg
    (fun x : ι → Bool => regularizedDistance P η u (bernoulliCubeVector x))
    (bernoulliCubeLaw ι p hp)
  rw [variance_eq_sub (bernoulliCubeLaw_memLp p hp _ 2)] at hVariance
  change 0 ≤ (∫ x : ι → Bool, regularizedDistance P η u (bernoulliCubeVector x) ^ 2
    ∂bernoulliCubeLaw ι p hp) - regularizedDistanceMean P η u p hp ^ 2 at hVariance
  rw [regularizedDistance_bernoulli_second_moment hP] at hVariance
  have hScale := regularizedDistanceScale_sq hP p hp η u
  have hMean := regularizedDistanceMean_nonneg P p hp η u
  have hScalePos : 0 ≤ regularizedDistanceScale P η u p := Real.sqrt_nonneg _
  nlinarith

omit [DecidableEq ι] in
theorem bernoulliCubeVector_norm_le (x : ι → Bool) :
    ‖bernoulliCubeVector x‖ ≤ Real.sqrt (Fintype.card ι) := by
  have hSq : ‖bernoulliCubeVector x‖ ^ 2 ≤ (Fintype.card ι : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _ : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        change ‖(cond (x i) 1 0 : ℂ)‖ ^ 2 ≤ 1
        cases x i <;> simp
      _ = _ := by simp
  have hCard : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hRoot := Real.sq_sqrt hCard
  have hRootPos := Real.sqrt_nonneg (Fintype.card ι : ℝ)
  nlinarith [norm_nonneg (bernoulliCubeVector x)]

theorem regularizedDistance_cube_bound {P : Matrix ι ι ℂ}
    (hP : IsPositiveMatrixContraction P) (η : ℝ) (u : EuclideanSpace ℂ ι) (x : ι → Bool) :
    regularizedDistance P η u (bernoulliCubeVector x) ≤
      Real.sqrt (η ^ 2 + (Real.sqrt (Fintype.card ι) + ‖u‖) ^ 2) :=
  regularizedDistance_le_euclidean_bound hP η u _ (bernoulliCubeVector_norm_le x)

end CircularLaw
