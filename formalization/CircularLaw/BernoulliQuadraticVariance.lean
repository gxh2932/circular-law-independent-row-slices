import CircularLaw.BernoulliMonomialOrthogonality
import CircularLaw.BernoulliLinearVariance
import Mathlib.Data.Finset.Prod

/-!
# Exact variance of centered Bernoulli quadratic forms

The diagonal and off-diagonal source monomials are integrated under
the actual independent cube law. Ordered off-diagonal pairs give the
equivalent coefficient `2 sigma^4` rather than `4 sigma^4` over `i<j`.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal InnerProductSpace ComplexOrder MatrixOrder

namespace CircularLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bernoulliQuadraticDiagonal (p : ℝ≥0) (a : Matrix ι ι ℝ) (x : ι → Bool) : ℝ :=
  ∑ i, a i i * bernoulliCenteredSquare p (x i)

def bernoulliQuadraticOffDiagonal (p : ℝ≥0) (a : Matrix ι ι ℝ) (x : ι → Bool) : ℝ :=
  ∑ ij ∈ (Finset.univ : Finset ι).offDiag,
    a ij.1 ij.2 * (bernoulliCenteredValue p (x ij.1) * bernoulliCenteredValue p (x ij.2))

theorem bernoulliQuadraticDiagonal_second_moment (p : ℝ≥0) (hp : p ≤ 1)
    (a : Matrix ι ι ℝ) :
    (∫ x, bernoulliQuadraticDiagonal p a x ^ 2 ∂bernoulliCubeLaw ι p hp) =
      (p * (1 - (p : ℝ)) * (1 - 4 * (p : ℝ) * (1 - (p : ℝ)))) * ∑ i, a i i ^ 2 := by
  have hExpand (x : ι → Bool) : bernoulliQuadraticDiagonal p a x ^ 2 =
      ∑ i, ∑ j, (a i i * a j j) *
        (bernoulliCenteredSquare p (x i) * bernoulliCenteredSquare p (x j)) := by
    simp only [bernoulliQuadraticDiagonal, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hExpand]
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite), integral_const_mul,
    bernoulliCubeLaw_square_covariance]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem bernoulliCubeLaw_pair_covariance_split (p : ℝ≥0) (hp : p ≤ 1)
    (ij kl : ι × ι) (hij : ij.1 ≠ ij.2) (hkl : kl.1 ≠ kl.2) :
    (∫ x, (bernoulliCenteredValue p (x ij.1) * bernoulliCenteredValue p (x ij.2)) *
      (bernoulliCenteredValue p (x kl.1) * bernoulliCenteredValue p (x kl.2))
      ∂bernoulliCubeLaw ι p hp) =
      (if ij = kl then (p * (1 - (p : ℝ))) ^ 2 else 0) +
        (if (ij.2, ij.1) = kl then (p * (1 - (p : ℝ))) ^ 2 else 0) := by
  rw [bernoulliCubeLaw_pair_covariance p hp ij.1 ij.2 kl.1 kl.2 hij hkl]
  have hFirst : ij = kl ↔ ij.1 = kl.1 ∧ ij.2 = kl.2 := Prod.ext_iff
  have hSecond : (ij.2, ij.1) = kl ↔ ij.1 = kl.2 ∧ ij.2 = kl.1 := by
    rw [Prod.ext_iff, and_comm]
  by_cases h₁ : ij = kl
  · have h₂ : (ij.2, ij.1) ≠ kl := by
      intro h
      have hEq := (hSecond.mp h).1
      have hEq₂ := (hFirst.mp h₁).2
      exact hij (hEq.trans hEq₂.symm)
    rw [if_pos (Or.inl (hFirst.mp h₁)), if_pos h₁, if_neg h₂, add_zero]
  · by_cases h₂ : (ij.2, ij.1) = kl
    · rw [if_pos (Or.inr (hSecond.mp h₂)), if_neg h₁, if_pos h₂, zero_add]
    · have hNeither : ¬ ((ij.1 = kl.1 ∧ ij.2 = kl.2) ∨ (ij.1 = kl.2 ∧ ij.2 = kl.1)) := by
        aesop
      rw [if_neg hNeither, if_neg h₁, if_neg h₂, add_zero]

theorem bernoulliQuadraticOffDiagonal_second_moment (p : ℝ≥0) (hp : p ≤ 1)
    (a : Matrix ι ι ℝ) (ha : ∀ i j, a i j = a j i) :
    (∫ x, bernoulliQuadraticOffDiagonal p a x ^ 2 ∂bernoulliCubeLaw ι p hp) =
      2 * (p * (1 - (p : ℝ))) ^ 2 *
        ∑ ij ∈ (Finset.univ : Finset ι).offDiag, a ij.1 ij.2 ^ 2 := by
  let S := (Finset.univ : Finset ι).offDiag
  have hExpand (x : ι → Bool) : bernoulliQuadraticOffDiagonal p a x ^ 2 =
      ∑ ij ∈ S, ∑ kl ∈ S, (a ij.1 ij.2 * a kl.1 kl.2) *
        ((bernoulliCenteredValue p (x ij.1) * bernoulliCenteredValue p (x ij.2)) *
          (bernoulliCenteredValue p (x kl.1) * bernoulliCenteredValue p (x kl.2))) := by
    simp only [bernoulliQuadraticOffDiagonal, pow_two, Finset.sum_mul, Finset.mul_sum, S]
    apply Finset.sum_congr rfl
    intro ij _
    apply Finset.sum_congr rfl
    intro kl _
    ring
  simp_rw [hExpand]
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite), integral_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hneq := (Finset.mem_offDiag.mp hij).2.2
  have hSwap : (ij.2, ij.1) ∈ S := Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hneq.symm⟩
  have hCov := fun kl (hkl : kl ∈ S) => bernoulliCubeLaw_pair_covariance_split p hp ij kl
    hneq (Finset.mem_offDiag.mp hkl).2.2
  have hRewrite :
      (∑ kl ∈ S, (a ij.1 ij.2 * a kl.1 kl.2) *
        (∫ x, (bernoulliCenteredValue p (x ij.1) * bernoulliCenteredValue p (x ij.2)) *
          (bernoulliCenteredValue p (x kl.1) * bernoulliCenteredValue p (x kl.2))
          ∂bernoulliCubeLaw ι p hp)) =
      ∑ kl ∈ S, (a ij.1 ij.2 * a kl.1 kl.2) *
        ((if ij = kl then (p * (1 - (p : ℝ))) ^ 2 else 0) +
          (if (ij.2, ij.1) = kl then (p * (1 - (p : ℝ))) ^ 2 else 0)) := by
    apply Finset.sum_congr rfl
    intro kl hkl
    rw [hCov kl hkl]
  rw [hRewrite]
  simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq,
    hij, hSwap, if_true]
  rw [ha ij.2 ij.1]
  ring

omit [DecidableEq ι] in
theorem bernoulliQuadratic_diagonal_offDiagonal_orthogonal (p : ℝ≥0) (hp : p ≤ 1)
    (a : Matrix ι ι ℝ) :
    (∫ x, bernoulliQuadraticDiagonal p a x * bernoulliQuadraticOffDiagonal p a x
      ∂bernoulliCubeLaw ι p hp) = 0 := by
  have hExpand (x : ι → Bool) :
      bernoulliQuadraticDiagonal p a x * bernoulliQuadraticOffDiagonal p a x =
      ∑ i, ∑ jk ∈ (Finset.univ : Finset ι).offDiag, (a i i * a jk.1 jk.2) *
        (bernoulliCenteredSquare p (x i) *
          (bernoulliCenteredValue p (x jk.1) * bernoulliCenteredValue p (x jk.2))) := by
    simp only [bernoulliQuadraticDiagonal, bernoulliQuadraticOffDiagonal,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro jk _
    ring
  simp_rw [hExpand]
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_eq_zero
  intro jk hjk
  rw [integral_const_mul, bernoulliCubeLaw_square_pair_orthogonal p hp i jk.1 jk.2
    (Finset.mem_offDiag.mp hjk).2.2, mul_zero]

def regularizedDistanceQuadraticTerm (P : Matrix ι ι ℂ) (p : ℝ≥0) (x : ι → Bool) : ℝ :=
  matrixEuclideanQuadratic P (bernoulliCenteredVector p x) - p * (1 - (p : ℝ)) * P.trace.re

omit [Fintype ι] [DecidableEq ι] in
theorem matrixHermitian_real_entries_symmetric {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (i j : ι) : (P i j).re = (P j i).re := by
  have h := congrArg Complex.re (hP.apply i j)
  simpa only [Complex.star_def, Complex.conj_re] using h.symm

omit [DecidableEq ι] in
theorem matrixHermitian_trace_square {P : Matrix ι ι ℂ} (hP : P.IsHermitian) :
    (P * P).trace.re = ∑ i, ∑ j, ‖P i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hP.apply j i]
  simp only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

theorem matrix_sum_diagonal_offDiagonal (f : ι × ι → ℝ) :
    (∑ i, ∑ j, f (i, j)) =
      (∑ i, f (i, i)) + ∑ ij ∈ (Finset.univ : Finset ι).offDiag, f ij := by
  rw [← Finset.sum_product, ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag Finset.univ), Finset.sum_diag]

theorem regularizedDistanceQuadraticTerm_eq (P : Matrix ι ι ℂ) (p : ℝ≥0) (x : ι → Bool) :
    regularizedDistanceQuadraticTerm P p x =
      bernoulliQuadraticDiagonal p (fun i j => (P i j).re) x +
        bernoulliQuadraticOffDiagonal p (fun i j => (P i j).re) x := by
  have hEntry (i j : ι) :
      (star (bernoulliCenteredVector p x i) * P i j * bernoulliCenteredVector p x j).re =
        (P i j).re * (bernoulliCenteredValue p (x i) * bernoulliCenteredValue p (x j)) := by
    simp only [bernoulliCenteredVector, Complex.star_def, Complex.conj_ofReal,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  simp only [regularizedDistanceQuadraticTerm, matrixEuclideanQuadratic_sum_entries, hEntry]
  rw [matrix_sum_diagonal_offDiagonal
    (fun ij => (P ij.1 ij.2).re * (bernoulliCenteredValue p (x ij.1) * bernoulliCenteredValue p (x ij.2)))]
  simp only [bernoulliQuadraticDiagonal, bernoulliQuadraticOffDiagonal, bernoulliCenteredSquare,
    mul_sub, Finset.sum_sub_distrib, Matrix.trace, Complex.re_sum, ← pow_two]
  simp only [← Finset.sum_mul, Matrix.diag_apply]
  ring

theorem regularizedDistanceQuadraticTerm_second_moment {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (p : ℝ≥0) (hp : p ≤ 1) :
    (∫ x, regularizedDistanceQuadraticTerm P p x ^ 2 ∂bernoulliCubeLaw ι p hp) =
      (p * (1 - (p : ℝ)) * (1 - 4 * (p : ℝ) * (1 - (p : ℝ)))) *
        ∑ i, (P i i).re ^ 2 +
      2 * (p * (1 - (p : ℝ))) ^ 2 *
        ∑ ij ∈ (Finset.univ : Finset ι).offDiag, (P ij.1 ij.2).re ^ 2 := by
  simp_rw [regularizedDistanceQuadraticTerm_eq, add_sq]
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite]
  simp only [mul_assoc, integral_const_mul, bernoulliQuadratic_diagonal_offDiagonal_orthogonal,
    mul_zero, add_zero, bernoulliQuadraticDiagonal_second_moment]
  rw [bernoulliQuadraticOffDiagonal_second_moment p hp _
    (matrixHermitian_real_entries_symmetric hP)]
  ring

theorem regularizedDistanceQuadraticTerm_mean (P : Matrix ι ι ℂ)
    (p : ℝ≥0) (hp : p ≤ 1) :
    (∫ x, regularizedDistanceQuadraticTerm P p x ∂bernoulliCubeLaw ι p hp) = 0 := by
  have hMoment := bernoulli_centered_quadratic_expectation p hp P 0
  simp only [add_zero] at hMoment
  simp only [regularizedDistanceQuadraticTerm]
  rw [integral_sub Integrable.of_finite Integrable.of_finite, hMoment]
  simp only [matrixEuclideanQuadratic, map_zero, inner_zero_left, Complex.zero_re,
    add_zero, integral_const, probReal_univ, one_smul, sub_self]

theorem regularizedDistanceQuadraticTerm_variance {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (p : ℝ≥0) (hp : p ≤ 1) :
    Var[regularizedDistanceQuadraticTerm P p; bernoulliCubeLaw ι p hp] =
      (p * (1 - (p : ℝ)) * (1 - 4 * (p : ℝ) * (1 - (p : ℝ)))) *
        ∑ i, (P i i).re ^ 2 +
      2 * (p * (1 - (p : ℝ))) ^ 2 *
        ∑ ij ∈ (Finset.univ : Finset ι).offDiag, (P ij.1 ij.2).re ^ 2 := by
  rw [variance_of_integral_eq_zero (bernoulliCubeLaw_memLp p hp _ 2).aemeasurable
    (regularizedDistanceQuadraticTerm_mean P p hp)]
  exact regularizedDistanceQuadraticTerm_second_moment hP p hp

theorem regularizedDistanceQuadraticTerm_second_moment_le {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (p : ℝ≥0) (hp : p ≤ 1) :
    (∫ x, regularizedDistanceQuadraticTerm P p x ^ 2 ∂bernoulliCubeLaw ι p hp) ≤
      p * (1 - (p : ℝ)) * (P * P).trace.re := by
  have h1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hσ : 0 ≤ p * (1 - (p : ℝ)) := mul_nonneg p.coe_nonneg (sub_nonneg.mpr h1)
  have hCoeff : p * (1 - (p : ℝ)) * (1 - 4 * (p : ℝ) * (1 - (p : ℝ))) ≤
      p * (1 - (p : ℝ)) := by nlinarith [sq_nonneg ((p : ℝ) * (1 - p))]
  have hOffCoeff : 2 * (p * (1 - (p : ℝ))) ^ 2 ≤ p * (1 - (p : ℝ)) := by
    nlinarith [bernoulli_variance_square_bound p hp, sq_nonneg ((p : ℝ) * (1 - p))]
  rw [regularizedDistanceQuadraticTerm_second_moment hP]
  calc
    _ ≤ p * (1 - (p : ℝ)) * (∑ i, (P i i).re ^ 2) +
        p * (1 - (p : ℝ)) *
          (∑ ij ∈ (Finset.univ : Finset ι).offDiag, (P ij.1 ij.2).re ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_right hCoeff (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
        (mul_le_mul_of_nonneg_right hOffCoeff (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = p * (1 - (p : ℝ)) * (∑ i, ∑ j, (P i j).re ^ 2) := by
      rw [matrix_sum_diagonal_offDiagonal (fun ij => (P ij.1 ij.2).re ^ 2)]
      ring
    _ ≤ p * (1 - (p : ℝ)) * (P * P).trace.re := by
      rw [matrixHermitian_trace_square hP]
      apply mul_le_mul_of_nonneg_left _ hσ
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [sq_nonneg (P i j).im]

end CircularLaw
