import CircularLaw.GraphGrowthBudget

/-!
# The source growth recurrence exits in fourth-power logarithmic time

The integer ceiling and recurrence k_(j+1)=k_j+g(k_j) are retained.
A uniform relative-increment bound gives an explicit exit-time estimate.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def sourceGraphRankSequence (C n d : ℝ) (k : ℕ) : ℕ → ℕ
  | 0 => k
  | j + 1 => sourceGraphRankSequence C n d k j +
    sourceGraphGrowth C n d (sourceGraphRankSequence C n d k j)

theorem source_graph_rank_sequence_zero (C n d : ℝ) (k : ℕ) :
    sourceGraphRankSequence C n d k 0 = k := rfl

theorem source_graph_rank_sequence_succ (C n d : ℝ) (k j : ℕ) :
    sourceGraphRankSequence C n d k (j + 1) = sourceGraphRankSequence C n d k j +
      sourceGraphGrowth C n d (sourceGraphRankSequence C n d k j) := rfl

theorem source_graph_rank_sequence_monotone (C n d : ℝ) (k : ℕ) :
    Monotone (sourceGraphRankSequence C n d k) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [source_graph_rank_sequence_succ]
  omega

theorem source_graph_rank_sequence_ge_initial (C n d : ℝ) (k j : ℕ) :
    k ≤ sourceGraphRankSequence C n d k j :=
  source_graph_rank_sequence_monotone C n d k (Nat.zero_le j)

theorem source_graph_rank_sequence_pos (C n d : ℝ) {k : ℕ} (hk : 0 < k) (j : ℕ) :
    0 < sourceGraphRankSequence C n d k j :=
  hk.trans_le (source_graph_rank_sequence_ge_initial C n d k j)

theorem source_graph_growth_relative_lower {C n d k x : ℝ}
    (hC : 0 < C) (hn : 0 < n) (hd : 1 ≤ d) (hk : 0 < k) (hkx : k ≤ x)
    (hLog : 1 ≤ Real.log (n / x)) :
    x / (2 * C * Real.log (n / k) ^ 3) ≤ (sourceGraphGrowth C n d x : ℝ) := by
  let L := Real.log (n / x)
  let L₀ := Real.log (n / k)
  have hx : 0 < x := hk.trans_le hkx
  have hdp : 0 < d := by linarith
  have hLp : 0 < L := by dsimp [L]; linarith
  have hLLe : L ≤ L₀ := Real.log_le_log (div_pos hn hx)
    (div_le_div_of_nonneg_left hn.le hk hkx)
  have hL₀ : 1 ≤ L₀ := hLog.trans hLLe
  have hL₀p : 0 < L₀ := by linarith
  have hSquare : L ^ 2 ≤ L₀ ^ 2 := (sq_le_sq₀ hLp.le hL₀p.le).mpr hLLe
  have hSum : d + L ≤ 2 * d * L₀ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) hL₀p.le,
      mul_nonneg (sub_nonneg.mpr hL₀) hdp.le]
  have hDen : L ^ 2 * (C * (d + L)) ≤ d * (2 * C * L₀ ^ 3) := by
    calc
      L ^ 2 * (C * (d + L)) ≤ L₀ ^ 2 * (C * (d + L)) :=
        mul_le_mul_of_nonneg_right hSquare (by positivity)
      _ ≤ L₀ ^ 2 * (C * (2 * d * L₀)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSum hC.le) (sq_nonneg _)
      _ = d * (2 * C * L₀ ^ 3) := by ring
  have hBase : x / (2 * C * L₀ ^ 3) ≤ sourceGraphGrowthBase C n d x := by
    unfold sourceGraphGrowthBase sourceGraphExpansion
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * C * L₀ ^ 3)
      (by positivity : 0 < Real.log (n / x) ^ 2 * (C * (d + Real.log (n / x))))).mpr
    have h := mul_le_mul_of_nonneg_left hDen hx.le
    dsimp [L] at h
    nlinarith
  exact hBase.trans (Nat.le_ceil _)

theorem log_one_add_half_lower {a : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) :
    a / 2 ≤ Real.log (1 + a) := by
  have hPos : 0 < 1 + a := by linarith
  have hInv := Real.one_sub_inv_le_log_of_pos hPos
  have hEq : 1 - (1 + a)⁻¹ = a / (1 + a) := by field_simp; ring
  rw [hEq] at hInv
  apply le_trans _ hInv
  apply (le_div_iff₀ hPos).mpr
  nlinarith [mul_nonneg ha (sub_nonneg.mpr haOne)]

set_option maxHeartbeats 1000000 in
theorem source_graph_rank_sequence_exits_by {C n d u : ℝ} {k : ℕ}
    (hC : 1 ≤ C) (hn : 0 < n) (hd : 1 ≤ d) (hk : 0 < k) (hu : 0 < u)
    (hku : (k : ℝ) ≤ u) (hLog : 1 ≤ Real.log (n / u)) :
    ∃ j ≤ Nat.ceil (4 * C * Real.log (n / k) ^ 4) + 1,
      u < (sourceGraphRankSequence C n d k j : ℝ) := by
  let L := Real.log (n / k)
  let a := 1 / (2 * C * L ^ 3)
  let T := Nat.ceil (4 * C * L ^ 4) + 1
  let r := sourceGraphRankSequence C n d k
  have hCp : 0 < C := by linarith
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hL : 1 ≤ L := hLog.trans (Real.log_le_log (div_pos hn hu)
    (div_le_div_of_nonneg_left hn.le hkReal hku))
  have hLp : 0 < L := by linarith
  have haPos : 0 < a := by dsimp [a]; positivity
  have hCube : 1 ≤ L ^ 3 := by nlinarith [sq_nonneg (L - 1)]
  have haOne : a ≤ 1 := by
    dsimp [a]
    apply (div_le_one (by positivity : 0 < 2 * C * L ^ 3)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (by positivity : 0 ≤ L ^ 3)]
  have hLogA := log_one_add_half_lower haPos.le haOne
  by_contra hNot
  have hAll : ∀ j ≤ T, (r j : ℝ) ≤ u := by
    intro j hj
    by_contra hBad
    exact hNot ⟨j, hj, lt_of_not_ge hBad⟩
  have hStep : ∀ j < T, Real.log (r j : ℝ) + a / 2 ≤ Real.log (r (j + 1) : ℝ) := by
    intro j hj
    have hrPos : 0 < (r j : ℝ) := by exact_mod_cast source_graph_rank_sequence_pos C n d hk j
    have hkr : (k : ℝ) ≤ r j := by exact_mod_cast source_graph_rank_sequence_ge_initial C n d k j
    have hLogR : 1 ≤ Real.log (n / r j) := hLog.trans
      (Real.log_le_log (div_pos hn hu) (div_le_div_of_nonneg_left hn.le hrPos (hAll j hj.le)))
    have hGrowth := source_graph_growth_relative_lower hCp hn hd hkReal hkr hLogR
    have hNext : (r j : ℝ) * (1 + a) ≤ (r (j + 1) : ℝ) := by
      have hEq : (r (j + 1) : ℝ) = (r j : ℝ) + sourceGraphGrowth C n d (r j) := by
        dsimp only [r]
        rw [source_graph_rank_sequence_succ, Nat.cast_add]
      rw [hEq]
      have hGrowthMul : (r j : ℝ) * a ≤ (sourceGraphGrowth C n d (r j) : ℝ) := by
        simpa only [a, L, div_eq_mul_inv, one_mul] using hGrowth
      nlinarith
    have hCompare := Real.log_le_log (mul_pos hrPos (by positivity : 0 < 1 + a)) hNext
    rw [Real.log_mul hrPos.ne' (by positivity : (1 + a) ≠ 0)] at hCompare
    linarith
  have hChain : ∀ j ≤ T, Real.log (k : ℝ) + (j : ℝ) * a / 2 ≤ Real.log (r j : ℝ) := by
    intro j hj
    induction j with
    | zero => simp [r, source_graph_rank_sequence_zero]
    | succ j ih =>
      have hPrev := ih (by omega : j ≤ T)
      have hNext := hStep j (by omega)
      simp only [Nat.cast_add, Nat.cast_one]
      linarith
  have hLast := hChain T le_rfl
  have hUpper := Real.log_le_log
    (by exact_mod_cast source_graph_rank_sequence_pos C n d hk T : 0 < (r T : ℝ))
    (hAll T le_rfl)
  have hT : 4 * C * L ^ 4 < (T : ℝ) := by
    have hCeil := Nat.le_ceil (4 * C * L ^ 4)
    dsimp [T]
    norm_cast
    push_cast
    linarith
  have hTime : L < (T : ℝ) * a / 2 := by
    have hDen : 0 < 4 * C * L ^ 3 := by positivity
    have h := (lt_div_iff₀ hDen).mpr
      (show L * (4 * C * L ^ 3) < (T : ℝ) by nlinarith [hT])
    convert h using 1
    dsimp [a]
    ring
  have hLogDiv : Real.log (n / u) = Real.log n - Real.log u := Real.log_div hn.ne' hu.ne'
  have hLId : L = Real.log n - Real.log (k : ℝ) := Real.log_div hn.ne' hkReal.ne'
  linarith

set_option maxHeartbeats 1000000 in
theorem source_graph_growth_first_exit_bound {C n d u : ℝ} {k : ℕ}
    (hC : 1 ≤ C) (hn : 0 < n) (hd : 1 ≤ d) (hk : 0 < k) (hu : 0 < u)
    (hLog : 1 ≤ Real.log (n / u)) :
    ∃ τ : ℕ, u < (sourceGraphRankSequence C n d k τ : ℝ) ∧
      (∀ j < τ, (sourceGraphRankSequence C n d k j : ℝ) ≤ u) ∧
        (τ : ℝ) ≤ (4 * C + 2) * Real.log (n / k) ^ 4 := by
  by_cases hku : (k : ℝ) ≤ u
  · obtain ⟨j, hj, hExit⟩ := source_graph_rank_sequence_exits_by hC hn hd hk hu hku hLog
    let hExists : ∃ j, u < (sourceGraphRankSequence C n d k j : ℝ) := ⟨j, hExit⟩
    let τ := Nat.find hExists
    have hTau := Nat.find_spec hExists
    have hTauLe : τ ≤ Nat.ceil (4 * C * Real.log (n / k) ^ 4) + 1 :=
      (Nat.find_min' hExists hExit).trans hj
    have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
    have hL : 1 ≤ Real.log (n / k) := hLog.trans (Real.log_le_log (div_pos hn hu)
      (div_le_div_of_nonneg_left hn.le hkReal hku))
    have hPow : 1 ≤ Real.log (n / k) ^ 4 := by nlinarith [sq_nonneg (Real.log (n / k) ^ 2 - 1)]
    have hCeil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * C * Real.log (n / k) ^ 4)
    have hCast : (τ : ℝ) ≤ (Nat.ceil (4 * C * Real.log (n / k) ^ 4) : ℝ) + 1 := by
      exact_mod_cast hTauLe
    refine ⟨τ, hTau, ?_, ?_⟩
    · intro i hi
      exact le_of_not_gt (Nat.find_min hExists hi)
    · nlinarith
  · refine ⟨0, ?_, ?_, ?_⟩
    · simpa only [source_graph_rank_sequence_zero] using lt_of_not_ge hku
    · intro j hj
      omega
    · simp only [Nat.cast_zero]
      positivity

end CircularLaw
