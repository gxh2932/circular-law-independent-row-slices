import CircularLaw.BernoulliSquareSmallExpansionProbability

/-!
# Small-set expansion with the original ambient normalization

The exposed matrix may have fewer rows than the original square matrix.
The degree and expansion threshold still use the original ambient size.
The fixed-set bound retains the exact number of diagonal rows, so that
sets containing an unmatched column can be counted separately.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators NNReal

namespace CircularLaw

theorem small_set_ambient_outside_rows_lower {N M ell q : ℕ}
    (hN : 0 < N) (hRows : 3 * (N : ℝ) / 4 ≤ M)
    (hq : q ≤ ell) (hqM : q ≤ M) (p : ℝ≥0)
    {d : ℝ} (hDegree : d = (N : ℝ) * p) (hd : 2 ≤ d)
    (hSmall : (ell : ℝ) * p ≤ 1 / 2) :
    d * ell / 2 ≤ ((M - q : ℕ) : ℝ) * ((ell : ℝ) * p) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hScaled := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg ell)
  have hMean := mul_le_mul_of_nonneg_left hSmall hn.le
  rw [hDegree] at hScaled
  have heN : (ell : ℝ) ≤ (N : ℝ) / 4 := by nlinarith
  have hqReal : (q : ℝ) ≤ ell := by exact_mod_cast hq
  have hOutside : (N : ℝ) / 2 ≤ M - q := by linarith
  rw [Nat.cast_sub hqM]
  have h := mul_le_mul_of_nonneg_right hOutside
    (mul_nonneg (Nat.cast_nonneg ell) p.coe_nonneg)
  rw [hDegree]
  nlinarith

theorem bernoulli_ambient_small_set_fixed_expansion_failure
    {ρ ι : Type*} [Fintype ρ] [Fintype ι] {N ell : ℕ}
    (hN : 0 < N) (hell : 0 < ell)
    (hRows : 3 * (N : ℝ) / 4 ≤ Fintype.card ρ)
    (p : ℝ≥0) (hp : p ≤ 1) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : 2 ≤ d)
    (hSmall : (ell : ℝ) * p ≤ 1 / 2) (hL : 1 ≤ Real.log ((N : ℝ) / ell))
    (hβ : 0 < β) (hβOne : β ≤ 1) (e : ρ ↪ ι) (S : Finset ι) (hS : S.card = ell) :
    (bernoulliCubeLaw (ρ × ι) p hp).real {x |
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) <
        sourceGraphExpansion N d ell} ≤
      Real.exp ((ell : ℝ) * (d / Real.log ((N : ℝ) / ell)) +
        ((bernoulliUniqueInsideRows e S).card : ℝ) *
          (Real.log (d + 1) - Real.log ((N : ℝ) / ell)) - d * ell / 8) := by
  let L := Real.log ((N : ℝ) / ell)
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have he : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hLp : 0 < L := by dsimp [L]; linarith
  have hRatio : 0 < (N : ℝ) / ell := div_pos hn he
  have hExp : Real.exp (-L) ≤ 1 / 2 := by
    apply (Real.exp_le_exp.mpr (by dsimp [L]; linarith : -L ≤ -1)).trans
    exact Real.exp_neg_one_lt_half.le
  have hExpEq : Real.exp (-L) = (ell : ℝ) / N := by
    rw [Real.exp_neg, Real.exp_log hRatio, inv_div]
  have hInsideLe : (bernoulliUniqueInsideRows e S).card ≤ ell :=
    (bernoulli_unique_inside_rows_card_le e S).trans_eq hS
  have hOutside := small_set_ambient_outside_rows_lower hN hRows hInsideLe
    (Finset.card_le_univ _) p hDegree hd hSmall
  have hFactorEq : (ell : ℝ) * p + Real.exp (-L) = Real.exp (Real.log (d + 1) - L) := by
    rw [hExpEq, Real.exp_sub, Real.exp_log (by linarith : 0 < d + 1), Real.exp_log hRatio, hDegree]
    field_simp
  have hTail := bernoulli_unique_neighbourhood_small_set_lower_tail p hp e S hβ hβOne hLp.le
    (by simpa only [hS] using hSmall) hExp (sourceGraphExpansion N d ell)
  simp only [hS] at hTail
  have hSubset : {x : ρ × ι → Bool |
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) <
        sourceGraphExpansion N d ell} ⊆ {x |
      ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) ≤
        sourceGraphExpansion N d ell} := by
    intro x hx
    change ((matrixUniqueNeighbourhood (bernoulliRectangularMatrix x) e β S).card : ℝ) <
      sourceGraphExpansion N d ell at hx
    exact hx.le
  apply ((measureReal_mono hSubset (measure_ne_top _ _)).trans hTail).trans
  rw [hFactorEq, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hThreshold : L * sourceGraphExpansion N d ell = (ell : ℝ) * (d / L) := by
    dsimp [sourceGraphExpansion, L]
    field_simp
  rw [hThreshold]
  dsimp only [L]
  linarith

theorem small_set_subset_entropy_cancellation {N M ell q : ℕ}
    (hN : 0 < N) (hMN : M ≤ N) (hell : 0 < ell) (hq : q ≤ ell) (hqM : q ≤ M)
    {d : ℝ} (hd : 1 ≤ d) :
    (M.choose q : ℝ) * Real.exp ((ell : ℝ) * (d / Real.log ((N : ℝ) / ell)) +
      (q : ℝ) * (Real.log (d + 1) - Real.log ((N : ℝ) / ell)) - d * ell / 8) ≤
      Real.exp ((ell : ℝ) * (2 + Real.log (d + 1) + d / Real.log ((N : ℝ) / ell) - d / 8)) := by
  have he : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hLog : 0 ≤ Real.log (d + 1) := Real.log_nonneg (by linarith)
  by_cases hqZero : q = 0
  · simp only [hqZero, Nat.choose_zero_right, Nat.cast_zero, Nat.cast_one, zero_mul, add_zero, one_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg he.le hLog]
  · have hqPos : 0 < q := Nat.pos_of_ne_zero hqZero
    have hqr : 0 < (q : ℝ) := by exact_mod_cast hqPos
    have hqe : (q : ℝ) ≤ ell := by exact_mod_cast hq
    have hLogEq : Real.log ((N : ℝ) / q) - Real.log ((N : ℝ) / ell) =
        Real.log ((ell : ℝ) / q) := by
      rw [Real.log_div hn.ne' hqr.ne', Real.log_div hn.ne' he.ne', Real.log_div he.ne' hqr.ne']
      ring
    have hRatio := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos he hqr)) hqr.le
    have hCancel : (q : ℝ) * ((ell : ℝ) / q - 1) = (ell : ℝ) - q := by field_simp
    rw [hCancel] at hRatio
    have hDegree := mul_le_mul_of_nonneg_right hqe (by linarith : 0 ≤ 1 + Real.log (d + 1))
    calc
      _ ≤ Real.exp ((q : ℝ) * (1 + Real.log ((N : ℝ) / q))) *
          Real.exp ((ell : ℝ) * (d / Real.log ((N : ℝ) / ell)) +
            (q : ℝ) * (Real.log (d + 1) - Real.log ((N : ℝ) / ell)) - d * ell / 8) :=
        mul_le_mul_of_nonneg_right (choose_le_ambient_log_entropy hMN hqPos hqM) (Real.exp_pos _).le
      _ ≤ _ := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        rw [← hLogEq] at hRatio
        nlinarith

theorem ambient_small_set_expansion_entropy_coefficient {d L : ℝ}
    (hd : 65536 ≤ d) (hL : 64 ≤ L) :
    2 + Real.log (d + 1) + d / L - d / 8 ≤ -d / 16 := by
  have hLog := small_set_expansion_log_degree_bound hd
  have hDiv : d / L ≤ d / 64 := div_le_div_of_nonneg_left (by linarith)
    (by norm_num : (0 : ℝ) < 64) hL
  linarith

end CircularLaw
