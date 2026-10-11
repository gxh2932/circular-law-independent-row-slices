import CircularLaw.IntegerGibbs
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Countable entropy and independent-copy dispersion

Nonnegative extended sums keep the definitions meaningful for every integer
law, including laws with infinite entropy or infinite first moment. The
comparison bound is first proved on every finite set of atoms.
-/

noncomputable section
open scoped ENNReal

namespace CircularLaw

def integerEntropyAtom (p : PMF ℤ) (j : ℤ) : ℝ :=
  -(p j).toReal * Real.log (p j).toReal

def integerEntropy (p : PMF ℤ) : ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal (integerEntropyAtom p j)

def integerMeanDistance (p : PMF ℤ) (r : ℤ) : ℝ≥0∞ :=
  ∑' j : ℤ, p j * ENNReal.ofReal |(j : ℝ) - (r : ℝ)|

def integerDispersion (p : PMF ℤ) : ℝ≥0∞ :=
  ∑' r : ℤ, p r * integerMeanDistance p r

theorem pmf_toReal_le_one (p : PMF ℤ) (j : ℤ) : (p j).toReal ≤ 1 := by
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one j)

theorem integerEntropyAtom_nonneg (p : PMF ℤ) (j : ℤ) :
    0 ≤ integerEntropyAtom p j := by
  have hLog := Real.log_nonpos ENNReal.toReal_nonneg (pmf_toReal_le_one p j)
  dsimp [integerEntropyAtom]
  nlinarith [ENNReal.toReal_nonneg (a := p j)]

theorem pmf_toReal_partial_mass (p : PMF ℤ) (S : Finset ℤ) :
    (∑ j ∈ S, (p j).toReal) ≤ 1 := by
  have hs := ENNReal.summable_toReal p.tsum_coe_ne_top
  have hTotal : (∑' j : ℤ, (p j).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe, ENNReal.toReal_one]
  exact (hs.sum_le_tsum S (fun _ _ => ENNReal.toReal_nonneg)).trans_eq hTotal

theorem entropy_atom_le_reference {a q : ℝ} (ha : 0 ≤ a) (hq : 0 < q) :
    -a * Real.log a ≤ q - a * Real.log q := by
  by_cases hzero : a = 0
  · simp only [hzero, neg_zero, zero_mul, sub_zero]
    exact hq.le
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hq haPos)
  have hscaled := mul_le_mul_of_nonneg_left hlog ha
  rw [Real.log_div hq.ne' hzero] at hscaled
  have hcancel : a * (q / a - 1) = q - a := by field_simp
  rw [hcancel] at hscaled
  nlinarith

theorem integerGibbsWeight_log {α : ℝ} (hα : 0 < α) (r j : ℤ) :
    Real.log ((α / 4) * integerGibbsKernel α r j) =
      -Real.log (4 / α) - α * |(j : ℝ) - (r : ℝ)| := by
  rw [Real.log_mul (by positivity) (integerGibbsKernel_pos α r j).ne',
    integerGibbsKernel, Real.log_exp, Real.log_div hα.ne' (by norm_num),
    Real.log_div (by norm_num) hα.ne']
  ring

theorem integer_partial_entropy_reference {α : ℝ} (hα : 0 < α) (hαOne : α ≤ 1)
    (p : PMF ℤ) (S : Finset ℤ) (r : ℤ) :
    (∑ j ∈ S, integerEntropyAtom p j) ≤ 1 + Real.log (4 / α) +
      α * (∑ j ∈ S, (p j).toReal * |(j : ℝ) - (r : ℝ)|) := by
  have hL : 0 ≤ Real.log (4 / α) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hα).mpr (by linarith)
  have hPoint : ∀ j : ℤ, integerEntropyAtom p j ≤
      (α / 4) * integerGibbsKernel α r j + Real.log (4 / α) * (p j).toReal +
        α * ((p j).toReal * |(j : ℝ) - (r : ℝ)|) := by
    intro j
    have hq : 0 < (α / 4) * integerGibbsKernel α r j :=
      mul_pos (by positivity) (integerGibbsKernel_pos α r j)
    have h := entropy_atom_le_reference (a := (p j).toReal) ENNReal.toReal_nonneg hq
    rw [integerGibbsWeight_log hα] at h
    dsimp [integerEntropyAtom]
    nlinarith only [h]
  have hMass := pmf_toReal_partial_mass p S
  have hRef := integerGibbsWeight_partial_mass hα hαOne r S
  have hMassL := mul_le_mul_of_nonneg_left hMass hL
  calc
    (∑ j ∈ S, integerEntropyAtom p j) ≤
        ∑ j ∈ S, ((α / 4) * integerGibbsKernel α r j +
          Real.log (4 / α) * (p j).toReal +
          α * ((p j).toReal * |(j : ℝ) - (r : ℝ)|)) :=
      Finset.sum_le_sum (fun j _ => hPoint j)
    _ = (∑ j ∈ S, (α / 4) * integerGibbsKernel α r j) +
        Real.log (4 / α) * (∑ j ∈ S, (p j).toReal) +
        α * (∑ j ∈ S, (p j).toReal * |(j : ℝ) - (r : ℝ)|) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 1 + Real.log (4 / α) +
        α * (∑ j ∈ S, (p j).toReal * |(j : ℝ) - (r : ℝ)|) := by
      nlinarith only [hRef, hMassL]

theorem integer_partial_entropy_mean_distance {α : ℝ} (hα : 0 < α) (hαOne : α ≤ 1)
    (p : PMF ℤ) (S : Finset ℤ) (r : ℤ) :
    (∑ j ∈ S, ENNReal.ofReal (integerEntropyAtom p j)) ≤
      ENNReal.ofReal (1 + Real.log (4 / α)) +
        ENNReal.ofReal α * integerMeanDistance p r := by
  have hL : 0 ≤ Real.log (4 / α) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hα).mpr (by linarith)
  have hC : 0 ≤ 1 + Real.log (4 / α) := by linarith
  have hMoment : 0 ≤ ∑ j ∈ S, (p j).toReal * |(j : ℝ) - (r : ℝ)| := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)
  have h := ENNReal.ofReal_le_ofReal (integer_partial_entropy_reference hα hαOne p S r)
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => integerEntropyAtom_nonneg p j),
    ENNReal.ofReal_add hC (mul_nonneg hα.le hMoment), ENNReal.ofReal_mul hα.le,
    ENNReal.ofReal_sum_of_nonneg (fun j _ =>
      mul_nonneg (ENNReal.toReal_nonneg (a := p j)) (abs_nonneg _))] at h
  have hMomentEq : (∑ j ∈ S, ENNReal.ofReal ((p j).toReal * |(j : ℝ) - (r : ℝ)|)) =
      ∑ j ∈ S, p j * ENNReal.ofReal |(j : ℝ) - (r : ℝ)| := by
    apply Finset.sum_congr rfl
    intro j _
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (p.apply_ne_top j)]
  rw [hMomentEq] at h
  exact h.trans (add_le_add (le_refl _)
    (mul_le_mul_right (ENNReal.sum_le_tsum S) (ENNReal.ofReal α)))

theorem integer_partial_entropy_dispersion {α : ℝ} (hα : 0 < α) (hαOne : α ≤ 1)
    (p : PMF ℤ) (S : Finset ℤ) :
    (∑ j ∈ S, ENNReal.ofReal (integerEntropyAtom p j)) ≤
      ENNReal.ofReal (1 + Real.log (4 / α)) + ENNReal.ofReal α * integerDispersion p := by
  have h := ENNReal.tsum_le_tsum (fun r : ℤ =>
    mul_le_mul_right (integer_partial_entropy_mean_distance hα hαOne p S r) (p r))
  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul] at h
  have hMoment : (∑' r : ℤ, p r * (ENNReal.ofReal α * integerMeanDistance p r)) =
      ENNReal.ofReal α * integerDispersion p := by
    simp only [mul_left_comm (p _) (ENNReal.ofReal α), ENNReal.tsum_mul_left,
      integerDispersion]
  rw [hMoment] at h
  exact h

theorem integer_entropy_gibbs_bound {α : ℝ} (hα : 0 < α) (hαOne : α ≤ 1) (p : PMF ℤ) :
    integerEntropy p ≤ ENNReal.ofReal (1 + Real.log (4 / α)) +
      ENNReal.ofReal α * integerDispersion p := by
  rw [integerEntropy, ENNReal.tsum_eq_iSup_sum]
  exact iSup_le (fun S => integer_partial_entropy_dispersion hα hαOne p S)

end CircularLaw
