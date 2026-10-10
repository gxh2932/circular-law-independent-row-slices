import CircularLaw.LLYThirdNetEntropy

/-!
# Literal rounded rank choices from LLY26a Section 6

The first rank retains its ceiling, the other ranks retain their floors,
and the stride uses the actual dimension-dependent expansion error.
These finite inequalities control the short first prefix even when
the first rank is one and that prefix is empty.
-/

noncomputable section
open Classical

namespace CircularLaw

def llySourceEpsilon (n d : ℕ) : ℝ := Real.sqrt (48 * Real.log (n : ℝ) / d)

def llySourceStride (n d : ℕ) : ℕ := ⌊1 / (100 * llySourceEpsilon n d)⌋₊

def llySourceFirstRank (n d : ℕ) (a : ℝ) : ℕ := ⌈a * llySourceEpsilon n d * n / d⌉₊

def llySourceSecondRank (n d : ℕ) (a : ℝ) : ℕ := ⌊a * n / (d : ℝ) ^ (3 / 4 : ℝ)⌋₊

def llySourceThirdRank (n : ℕ) (a : ℝ) : ℕ := ⌊a * n⌋₊

theorem lly_source_epsilon_pos {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) :
    0 < llySourceEpsilon n d := by
  apply Real.sqrt_pos.mpr
  exact div_pos (mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)))
    (by exact_mod_cast hd)

theorem lly_source_epsilon_upper {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {C t : ℝ} (ht : 0 ≤ t) (hC : 48 ≤ C * t ^ 2) (hDegree : C * Real.log (n : ℝ) ≤ d) :
    llySourceEpsilon n d ≤ t := by
  have hLog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)
  have hDegreeScaled := mul_le_mul_of_nonneg_right hDegree (sq_nonneg t)
  have hConstScaled := mul_le_mul_of_nonneg_right hC hLog.le
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) ht).mp
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 48 * Real.log (n : ℝ) / d)]
  apply (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  nlinarith

theorem lly_source_stride_ge_two {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {C : ℝ} (hC : 1920000 ≤ C) (hDegree : C * Real.log (n : ℝ) ≤ d) :
    2 ≤ llySourceStride n d := by
  have hEps := lly_source_epsilon_upper hn hd (by norm_num : (0 : ℝ) ≤ 1 / 200)
    (by nlinarith : (48 : ℝ) ≤ C * (1 / 200 : ℝ) ^ 2) hDegree
  have hPos := lly_source_epsilon_pos hn hd
  apply Nat.le_floor
  apply (le_div_iff₀ (by positivity : 0 < 100 * llySourceEpsilon n d)).mpr
  norm_num
  linarith

theorem lly_source_first_rank_pos {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {a : ℝ} (ha : 0 < a) : 0 < llySourceFirstRank n d a := by
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos (mul_pos ha (lly_source_epsilon_pos hn hd))
    (by exact_mod_cast (show 0 < n by omega))) (by exact_mod_cast hd)

theorem lly_source_first_rank_prev_upper {n d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 ≤ a) :
    ((llySourceFirstRank n d a - 1 : ℕ) : ℝ) ≤ a * llySourceEpsilon n d * n / d := by
  have hRatio : 0 ≤ a * llySourceEpsilon n d * n / d := by
    unfold llySourceEpsilon
    positivity
  by_cases hZero : llySourceFirstRank n d a = 0
  · simpa only [hZero, Nat.zero_sub, Nat.cast_zero] using hRatio
  · have hCeil := Nat.ceil_lt_add_one hRatio
    rw [Nat.cast_sub (by omega : 1 ≤ llySourceFirstRank n d a), Nat.cast_one]
    change (⌈a * llySourceEpsilon n d * n / d⌉₊ : ℝ) - 1 ≤ _
    linarith

theorem lly_source_first_rank_le_dimension {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {C a : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) (hC : 48 ≤ C)
    (hDegree : C * Real.log (n : ℝ) ≤ d) : llySourceFirstRank n d a ≤ n := by
  have hEps := lly_source_epsilon_upper hn hd (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [one_pow, mul_one] using hC) hDegree
  have hEpsNonneg : 0 ≤ llySourceEpsilon n d := Real.sqrt_nonneg _
  have hCoeff : a * llySourceEpsilon n d ≤ 1 := by nlinarith
  have hNumerator := mul_le_mul_of_nonneg_right hCoeff (Nat.cast_nonneg (α := ℝ) n)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  nlinarith

theorem lly_source_second_rank_upper {n d : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    (llySourceSecondRank n d a : ℝ) ≤ a * n / (d : ℝ) ^ (3 / 4 : ℝ) :=
  Nat.floor_le (by positivity)

theorem lly_source_second_rank_density_lower {n d : ℕ} {a : ℝ}
    (hSize : 2 ≤ a * n / (d : ℝ) ^ (3 / 4 : ℝ)) :
    a * n / (d : ℝ) ^ (3 / 4 : ℝ) ≤ 2 * llySourceSecondRank n d a := by
  have hFloor := Nat.lt_floor_add_one (a * n / (d : ℝ) ^ (3 / 4 : ℝ))
  change _ ≤ 2 * (⌊a * n / (d : ℝ) ^ (3 / 4 : ℝ)⌋₊ : ℝ)
  linarith

theorem lly_source_third_rank_upper {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    (llySourceThirdRank n a : ℝ) ≤ a * n := Nat.floor_le (by positivity)

theorem lly_source_scale_count_log_budget {n ℓ r k : ℕ} (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ)
    (hRank : ℓ ^ r < k) (hkn : k ≤ n) : ((r : ℝ) + 2) * Real.log 2 ≤ 3 * Real.log (n : ℝ) := by
  have hPow : (0 : ℝ) < (ℓ : ℝ) ^ r := pow_pos (by exact_mod_cast (show 0 < ℓ by omega)) _
  have hPowN : (ℓ : ℝ) ^ r < n := by exact_mod_cast (lt_of_lt_of_le hRank hkn)
  have hLogPow := Real.log_lt_log hPow hPowN
  rw [Real.log_pow] at hLogPow
  have hLogStride : Real.log 2 ≤ Real.log (ℓ : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hℓ)
  have hScaled := mul_le_mul_of_nonneg_left hLogStride (Nat.cast_nonneg (α := ℝ) r)
  have hLogN : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  nlinarith

theorem lly_source_first_prefix_cost {n d ℓ r : ℕ} (hn : 2 ≤ n) (hd : 0 < d) (hℓ : 2 ≤ ℓ)
    {C a : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) (hC : 48 ≤ C)
    (hDegree : C * Real.log (n : ℝ) ≤ d) (hCost : 12288 * a ≤ C * Real.log 2)
    (hRank : llySourceFirstRank n d a = 1 ∨ ℓ ^ r < llySourceFirstRank n d a) :
    ((r : ℝ) + 2) * (llySourceFirstRank n d a - 1 : ℕ) ≤ (n : ℝ) / 4096 := by
  rcases hRank with hOne | hRank
  · simp only [hOne, Nat.sub_self, Nat.cast_zero, mul_zero]
    positivity
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hScale := lly_source_scale_count_log_budget hn hℓ hRank
    (lly_source_first_rank_le_dimension hn hd ha haOne hC hDegree)
  have hEps := lly_source_epsilon_upper hn hd (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [one_pow, mul_one] using hC) hDegree
  have hPrev := lly_source_first_rank_prev_upper (n := n) hd ha
  have hPrevD : ((llySourceFirstRank n d a - 1 : ℕ) : ℝ) * d ≤ a * n := by
    have h := (le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mp hPrev
    have hCoeff := mul_le_mul_of_nonneg_left hEps (by positivity : 0 ≤ a * (n : ℝ))
    nlinarith
  have hLogN := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega) : (1 : ℝ) ≤ n)
  have hFirstScaled := mul_le_mul_of_nonneg_left hPrevD
    (by positivity : 0 ≤ ((r : ℝ) + 2) * Real.log 2)
  have hScaleScaled := mul_le_mul_of_nonneg_right hScale (by positivity : 0 ≤ a * (n : ℝ))
  have hConstScaled := mul_le_mul_of_nonneg_right hCost (by positivity : 0 ≤ (n : ℝ) * Real.log n)
  have hDegreeScaled := mul_le_mul_of_nonneg_right hDegree (by positivity : 0 ≤ (n : ℝ) * Real.log 2)
  have hBound : (((r : ℝ) + 2) * (llySourceFirstRank n d a - 1 : ℕ)) *
      ((d : ℝ) * Real.log 2) ≤ ((n : ℝ) / 4096) * ((d : ℝ) * Real.log 2) := by nlinarith
  exact (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < (d : ℝ) * Real.log 2)).mp hBound

end CircularLaw
