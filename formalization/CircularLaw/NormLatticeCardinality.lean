import CircularLaw.GaussianLattice
import CircularLaw.FiniteMean

/-!
# Dimension-exponential cardinality of the bounded integer lattice

Inside any finite integer box, the vectors with squared mass at most
`81*n` number at most `128^n`. Gaussian weights factor over the literal
finite coordinate product. Each retained vector has weight at least
`exp(-n)`, and the full coordinate sum is at most 37.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

abbrev NormLatticeCoordinate (R : ℕ) := {q : ℤ // q ∈ Finset.Icc (-(R : ℤ)) (R : ℤ)}

abbrev NormLatticeBox (n R : ℕ) := Fin n → NormLatticeCoordinate R

def normLatticeSquaredMass {n R : ℕ} (q : NormLatticeBox n R) : ℝ := ∑ i, ((q i).val : ℝ) ^ 2

def normLatticeWeight {n R : ℕ} (q : NormLatticeBox n R) : ℝ := Real.exp (-normLatticeSquaredMass q / 81)

def normBoundedLattice (n R : ℕ) : Finset (NormLatticeBox n R) :=
  Finset.univ.filter (fun q => normLatticeSquaredMass q ≤ 81 * (n : ℝ))

theorem normLatticeWeight_prod {n R : ℕ} (q : NormLatticeBox n R) :
    normLatticeWeight q = ∏ i : Fin n, Real.exp (-((q i).val : ℝ) ^ 2 / 81) := by
  unfold normLatticeWeight normLatticeSquaredMass
  have hExponent : -(∑ i : Fin n, ((q i).val : ℝ) ^ 2) / 81 =
      ∑ i : Fin n, -((q i).val : ℝ) ^ 2 / 81 := by
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
  rw [hExponent, Real.exp_sum]

theorem normLatticeCoordinate_gaussian_sum_le (R : ℕ) :
    (∑ q : NormLatticeCoordinate R, Real.exp (-(q.val : ℝ) ^ 2 / 81)) ≤ 37 := by
  have hSummable := gaussian_integer_summable (by norm_num : (0 : ℝ) < 1 / 81)
  have hAll := gaussian_integer_tsum_le (by norm_num : (0 : ℝ) < 1 / 81)
  have hRoot : Real.sqrt (Real.pi / (1 / 81 : ℝ)) ≤ 18 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · have hPi := Real.pi_lt_four.le
      norm_num
      nlinarith
  calc
    _ = ∑ q ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), Real.exp (-(q : ℝ) ^ 2 / 81) :=
      Finset.sum_coe_sort _ _
    _ ≤ ∑' q : ℤ, Real.exp (-(q : ℝ) ^ 2 / 81) := by
      apply Summable.sum_le_tsum _ (fun q _ => (Real.exp_pos _).le)
      convert hSummable using 1
      funext q
      congr 1
      ring
    _ ≤ 1 + 2 * Real.sqrt (Real.pi / (1 / 81 : ℝ)) := by
      convert hAll using 1
      congr 1
      funext q
      congr 1
      ring
    _ ≤ 37 := by linarith

theorem normLatticeBox_gaussian_sum_le (n R : ℕ) :
    (∑ q : NormLatticeBox n R, normLatticeWeight q) ≤ (37 : ℝ) ^ n := by
  calc
    _ = ∑ q : NormLatticeBox n R, ∏ i : Fin n, Real.exp (-((q i).val : ℝ) ^ 2 / 81) := by
      apply Finset.sum_congr rfl
      intro q _
      exact normLatticeWeight_prod q
    _ = ∏ _i : Fin n, ∑ q : NormLatticeCoordinate R, Real.exp (-(q.val : ℝ) ^ 2 / 81) :=
      (Fintype.prod_sum (fun _i : Fin n => fun q : NormLatticeCoordinate R => Real.exp (-(q.val : ℝ) ^ 2 / 81))).symm
    _ ≤ ∏ _i : Fin n, (37 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Finset.sum_nonneg (fun q _ => (Real.exp_pos _).le)
      · intro i _
        exact normLatticeCoordinate_gaussian_sum_le R
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem normBoundedLattice_weight_lower {n R : ℕ} {q : NormLatticeBox n R}
    (hq : q ∈ normBoundedLattice n R) : Real.exp (-(n : ℝ)) ≤ normLatticeWeight q := by
  have hMass : normLatticeSquaredMass q ≤ 81 * (n : ℝ) := (Finset.mem_filter.mp hq).2
  apply Real.exp_le_exp.mpr
  change -(n : ℝ) ≤ -normLatticeSquaredMass q / 81
  linarith

theorem normBoundedLattice_weighted_card_le (n R : ℕ) :
    ((normBoundedLattice n R).card : ℝ) * Real.exp (-(n : ℝ)) ≤ (37 : ℝ) ^ n := by
  calc
    _ = ∑ _q ∈ normBoundedLattice n R, Real.exp (-(n : ℝ)) := by simp
    _ ≤ ∑ q ∈ normBoundedLattice n R, normLatticeWeight q :=
      Finset.sum_le_sum (fun _ hq => normBoundedLattice_weight_lower hq)
    _ ≤ ∑ q : NormLatticeBox n R, normLatticeWeight q :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun q _ _ => (Real.exp_pos _).le)
    _ ≤ _ := normLatticeBox_gaussian_sum_le n R

theorem normBoundedLattice_card_le (n R : ℕ) : (normBoundedLattice n R).card ≤ 128 ^ n := by
  have hWeighted := normBoundedLattice_weighted_card_le n R
  have hExpInverse : Real.exp (-(n : ℝ)) * Real.exp (n : ℝ) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hExpPower : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
    simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) n
  have hBase : Real.exp (1 : ℝ) * 37 ≤ 128 := by
    have h := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (by norm_num : (0 : ℝ) ≤ 37)
    linarith
  have hCardReal : ((normBoundedLattice n R).card : ℝ) ≤ (128 : ℝ) ^ n := by
    calc
      _ = (((normBoundedLattice n R).card : ℝ) * Real.exp (-(n : ℝ))) * Real.exp (n : ℝ) := by
        rw [mul_assoc, hExpInverse, mul_one]
      _ ≤ (37 : ℝ) ^ n * Real.exp (n : ℝ) := mul_le_mul_of_nonneg_right hWeighted (Real.exp_nonneg _)
      _ = (Real.exp 1 * 37) ^ n := by rw [hExpPower, mul_pow]; ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hBase n
  exact_mod_cast hCardReal

end CircularLaw
