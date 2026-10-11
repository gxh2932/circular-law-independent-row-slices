import CircularLaw.BernoulliSliceConditioning
import CircularLaw.BinomialStirlingMass

/-!
# The conditioning mass at the literal parameter p=d/n

For every positive degree at most the dimension, the actual support-size
event has probability at least `1/(4*exp(1)^2*sqrt(d))`. The full-support
endpoint is treated separately and has probability exactly one.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace CircularLaw

def rowBernoulliParameter (n d : ℕ) : ℝ≥0 := (d : ℝ≥0) / n

theorem rowBernoulliParameter_coe (n d : ℕ) :
    (rowBernoulliParameter n d : ℝ) = (d : ℝ) / n := by
  simp only [rowBernoulliParameter, NNReal.coe_div, NNReal.coe_natCast]

theorem rowBernoulliParameter_le_one {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    rowBernoulliParameter n d ≤ 1 := by
  have hReal : (d : ℝ) / n ≤ 1 := (div_le_one (by positivity : (0 : ℝ) < n)).mpr (by exact_mod_cast hdn)
  exact_mod_cast (rowBernoulliParameter_coe n d).symm ▸ hReal

theorem bernoulliSliceMass_eq_split {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    bernoulliSliceMass n d (rowBernoulliParameter n d) = splitBinomialMass d (n - d) := by
  have hComplement : 1 - (d : ℝ) / n = ((n - d : ℕ) : ℝ) / n := by
    rw [Nat.cast_sub hdn]
    field_simp
  have hSum : (d : ℝ) + (n - d : ℕ) = (n : ℝ) := by
    rw [Nat.cast_sub hdn]
    ring
  simp only [bernoulliSliceMass, bernoulliSliceAtomWeight, rowBernoulliParameter_coe,
    splitBinomialMass, Nat.add_sub_of_le hdn, hComplement, hSum]
  ring

theorem bernoulliSliceMass_positive_degree_lower {n d : ℕ} (hd : 0 < d) (hdn : d < n) :
    1 / (4 * Real.exp 1 ^ 2 * Real.sqrt (d : ℝ)) ≤
      bernoulliSliceMass n d (rowBernoulliParameter n d) := by
  rw [bernoulliSliceMass_eq_split (by omega) hdn.le]
  exact splitBinomialMass_lower hd (Nat.sub_pos_of_lt hdn)

theorem bernoulliSliceMass_full_support {n : ℕ} (hn : 0 < n) :
    bernoulliSliceMass n n (rowBernoulliParameter n n) = 1 := by
  have hp : (rowBernoulliParameter n n : ℝ) = 1 := by
    rw [rowBernoulliParameter_coe, div_self (by positivity : (n : ℝ) ≠ 0)]
  simp only [bernoulliSliceMass, bernoulliSliceAtomWeight, hp, Nat.choose_self,
    Nat.cast_one, one_pow, Nat.sub_self, pow_zero, mul_one]

theorem bernoulliSliceMass_lower {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    1 / (4 * Real.exp 1 ^ 2 * Real.sqrt (d : ℝ)) ≤
      bernoulliSliceMass n d (rowBernoulliParameter n d) := by
  obtain hlt | rfl := lt_or_eq_of_le hdn
  · exact bernoulliSliceMass_positive_degree_lower hd hlt
  · rw [bernoulliSliceMass_full_support hd]
    have hRoot : 1 ≤ Real.sqrt (d : ℝ) := by
      have hnR : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d), Real.sqrt_nonneg (d : ℝ)]
    have hExp : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    apply (div_le_iff₀ (by positivity : 0 < 4 * Real.exp 1 ^ 2 * Real.sqrt (d : ℝ))).mpr
    nlinarith [sq_nonneg (Real.exp 1 - 1)]

theorem bernoulliSliceMass_pos {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    0 < bernoulliSliceMass n d (rowBernoulliParameter n d) :=
  (by positivity : 0 < 1 / (4 * Real.exp 1 ^ 2 * Real.sqrt (d : ℝ))).trans_le
    (bernoulliSliceMass_lower hd hdn)

theorem bernoulliCubeLaw_support_size_lower {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    1 / (4 * Real.exp 1 ^ 2 * Real.sqrt (d : ℝ)) ≤
      (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
        (rowBernoulliParameter_le_one (by omega) hdn)).real {x | bernoulliSupportSize x = d} := by
  rw [bernoulliCubeLaw_fiber_mass]
  exact bernoulliSliceMass_lower hd hdn

theorem bernoulliSlice_conditional_law_at_mean {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    (bernoulliCubeLaw (Fin n) (rowBernoulliParameter n d)
      (rowBernoulliParameter_le_one (by omega) hdn))[|{x | bernoulliSupportSize x = d}] =
        (rowSliceLaw n d).map rowSliceBoolRow :=
  bernoulliSlice_conditional_law hdn _ _ (bernoulliSliceMass_pos hd hdn)

end CircularLaw
