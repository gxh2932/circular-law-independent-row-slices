import CircularLaw.BernoulliCubeLaw
import CircularLaw.RegularizedDistanceGeometry

/-!
# The regularized-distance second moment under the actual Bernoulli law

Centered coordinate covariance cancels every cross-coordinate and linear
term in the quadratic form. Its expectation is the variance times the
literal matrix trace, plus the deterministic shifted quadratic form.
This proves Section 8's exact `D_P^2` identity for the full comparator law.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace ComplexOrder MatrixOrder

namespace CircularLaw

section Cube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bernoulliCubeVector (x : ι → Bool) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => cond (x i) 1 0)

def bernoulliCenteredVector (p : ℝ≥0) (x : ι → Bool) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => (bernoulliCenteredValue p (x i) : ℂ))

def bernoulliMeanVector (ι : Type*) [Fintype ι] (p : ℝ≥0) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun _ => (p : ℝ))

omit [DecidableEq ι] in
theorem bernoulliCubeVector_centered_shift (p : ℝ≥0) (x : ι → Bool) (u : EuclideanSpace ℂ ι) :
    bernoulliCubeVector x + u = bernoulliCenteredVector p x + (u + bernoulliMeanVector ι p) := by
  ext i
  simp only [bernoulliCubeVector, bernoulliCenteredVector, bernoulliMeanVector,
    PiLp.add_apply, bernoulliCenteredValue, Complex.ofReal_sub]
  cases x i <;> simp

theorem bernoulli_shifted_entry_moment (p : ℝ≥0) (hp : p ≤ 1)
    (i j : ι) (a u v : ℂ) :
    (∫ x : ι → Bool,
      (star ((bernoulliCenteredValue p (x i) : ℂ) + u) * a *
        ((bernoulliCenteredValue p (x j) : ℂ) + v)).re ∂bernoulliCubeLaw ι p hp) =
      (if i = j then p * (1 - (p : ℝ)) else 0) * a.re + (star u * a * v).re := by
  have hExpand (x : ι → Bool) :
      (star ((bernoulliCenteredValue p (x i) : ℂ) + u) * a *
        ((bernoulliCenteredValue p (x j) : ℂ) + v)).re =
      a.re * (bernoulliCenteredValue p (x i) * bernoulliCenteredValue p (x j)) +
        (a * v).re * bernoulliCenteredValue p (x i) +
        (star u * a).re * bernoulliCenteredValue p (x j) + (star u * a * v).re := by
    simp only [star_add, Complex.star_def, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    ring
  simp_rw [hExpand]
  rw [integral_add .of_finite .of_finite, integral_add .of_finite .of_finite,
    integral_add .of_finite .of_finite]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    bernoulliCubeLaw_centered_coordinate_product,
    bernoulliCubeLaw_centered_coordinate_mean, bernoulliCubeLaw_centered_coordinate_mean]
  simp only [mul_zero, add_zero, integral_const, probReal_univ, one_smul]
  ring

theorem bernoulli_centered_quadratic_expectation (p : ℝ≥0) (hp : p ≤ 1)
    (P : Matrix ι ι ℂ) (u : EuclideanSpace ℂ ι) :
    (∫ x : ι → Bool, matrixEuclideanQuadratic P (bernoulliCenteredVector p x + u)
      ∂bernoulliCubeLaw ι p hp) = p * (1 - (p : ℝ)) * P.trace.re + matrixEuclideanQuadratic P u := by
  simp_rw [matrixEuclideanQuadratic_sum_entries]
  simp only [bernoulliCenteredVector, PiLp.add_apply]
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite), bernoulli_shifted_entry_moment,
    Finset.sum_add_distrib]
  have hDiagonal : (∑ i : ι, ∑ j : ι, (if i = j then p * (1 - (p : ℝ)) else 0) * (P i j).re) =
      p * (1 - (p : ℝ)) * P.trace.re := by
    simp only [ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Matrix.trace, Complex.re_sum, Finset.mul_sum]
    rfl
  rw [hDiagonal]

theorem bernoulli_quadratic_expectation (p : ℝ≥0) (hp : p ≤ 1)
    (P : Matrix ι ι ℂ) (u : EuclideanSpace ℂ ι) :
    (∫ x : ι → Bool, matrixEuclideanQuadratic P (bernoulliCubeVector x + u)
      ∂bernoulliCubeLaw ι p hp) =
      p * (1 - (p : ℝ)) * P.trace.re + matrixEuclideanQuadratic P (u + bernoulliMeanVector ι p) := by
  have hShift (x : ι → Bool) := bernoulliCubeVector_centered_shift p x u
  simp only [hShift]
  exact bernoulli_centered_quadratic_expectation p hp P _

def regularizedDistanceScaleSq (P : Matrix ι ι ℂ) (η : ℝ) (u : EuclideanSpace ℂ ι) (p : ℝ≥0) : ℝ :=
  η ^ 2 + p * (1 - (p : ℝ)) * P.trace.re + matrixEuclideanQuadratic P (u + bernoulliMeanVector ι p)

theorem regularizedDistance_bernoulli_second_moment {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    (p : ℝ≥0) (hp : p ≤ 1) (η : ℝ) (u : EuclideanSpace ℂ ι) :
    (∫ x : ι → Bool, regularizedDistance P η u (bernoulliCubeVector x) ^ 2
      ∂bernoulliCubeLaw ι p hp) = regularizedDistanceScaleSq P η u p := by
  simp_rw [regularizedDistance_sq hP]
  rw [integral_add .of_finite .of_finite, bernoulli_quadratic_expectation]
  simp only [integral_const, probReal_univ, one_smul, regularizedDistanceScaleSq]
  ring

end Cube

end CircularLaw
