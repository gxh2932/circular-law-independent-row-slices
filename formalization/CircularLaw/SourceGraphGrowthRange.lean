import CircularLaw.GraphGrowthIteration

/-!
# The source terminal range and valid integer growth ranks

The terminal scale n*log(log d)/(2*d) satisfies the logarithmic range
needed by the exit-time theorem. The ceiling gives a next-rank upper
bound of twice the current rank.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def sourceGraphTerminalScale (n d : ℝ) : ℝ := n / (2 * d) * Real.log (Real.log d)

theorem log_le_half_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have hRoot := Real.sqrt_pos.mpr hx
  have hLog := Real.log_le_sub_one_of_pos hRoot
  rw [Real.log_sqrt hx.le] at hLog
  nlinarith [Real.sq_sqrt hx.le, sq_nonneg (Real.sqrt x - 2)]

theorem source_graph_terminal_range {n d : ℝ} (hn : 0 < n)
    (hd : Real.exp (Real.exp 1) ≤ d) :
    0 < sourceGraphTerminalScale n d ∧ sourceGraphTerminalScale n d ≤ n / 4 ∧
      1 ≤ Real.log (n / sourceGraphTerminalScale n d) := by
  have hdp : 0 < d := (Real.exp_pos _).trans_le hd
  have hLogD : Real.exp 1 ≤ Real.log d := (Real.le_log_iff_exp_le hdp).mpr hd
  have hLogDp : 0 < Real.log d := (Real.exp_pos _).trans_le hLogD
  have hLogLogD : 1 ≤ Real.log (Real.log d) := (Real.le_log_iff_exp_le hLogDp).mpr hLogD
  have hu : 0 < sourceGraphTerminalScale n d := by
    unfold sourceGraphTerminalScale
    positivity
  have hHalf : Real.log (Real.log d) ≤ d / 2 :=
    (Real.log_le_self hLogDp.le).trans (log_le_half_of_pos hdp)
  have hUpper : sourceGraphTerminalScale n d ≤ n / 4 := by
    unfold sourceGraphTerminalScale
    have h := mul_le_mul_of_nonneg_left hHalf (div_pos hn (by positivity : 0 < 2 * d)).le
    calc
      _ ≤ n / (2 * d) * (d / 2) := h
      _ = n / 4 := by field_simp; norm_num
  have hRatio : 4 ≤ n / sourceGraphTerminalScale n d := by
    apply (le_div_iff₀ hu).mpr
    linarith
  have hLog := (Real.le_log_iff_exp_le (div_pos hn hu)).mpr
    (Real.exp_one_lt_three.le.trans (by linarith : (3 : ℝ) ≤ n / sourceGraphTerminalScale n d))
  exact ⟨hu, hUpper, hLog⟩

theorem source_graph_growth_next_rank_le {C n d : ℝ} {ell : ℕ}
    (hC : 1 ≤ C) (hd : 1 ≤ d) (hEll : 0 < ell)
    (hLog : 1 ≤ Real.log (n / ell)) :
    ell + sourceGraphGrowth C n d ell ≤ 2 * ell := by
  have hEllReal : 0 < (ell : ℝ) := by exact_mod_cast hEll
  have hBase := source_graph_growth_base_le_coordinate hC hd hEllReal hLog
  have hCeil : sourceGraphGrowth C n d ell ≤ ell := Nat.ceil_le.mpr hBase
  omega

theorem source_graph_growth_next_rank_valid {C n d u : ℝ} {ell m : ℕ}
    (hC : 1 ≤ C) (hd : 1 ≤ d) (hEll : 0 < ell) (hEllU : (ell : ℝ) ≤ u)
    (hLog : 1 ≤ Real.log (n / ell)) (hAmbient : 2 * u ≤ (m : ℝ)) :
    ell + sourceGraphGrowth C n d ell ≤ m := by
  have hNext := source_graph_growth_next_rank_le hC hd hEll hLog
  have hNextReal : ((ell + sourceGraphGrowth C n d ell : ℕ) : ℝ) ≤ 2 * ell := by
    exact_mod_cast hNext
  have hLe : ((ell + sourceGraphGrowth C n d ell : ℕ) : ℝ) ≤ m := by linarith
  exact_mod_cast hLe

theorem source_graph_terminal_first_exit_bound {C n d : ℝ} {k : ℕ}
    (hC : 1 ≤ C) (hn : 0 < n) (hd : Real.exp (Real.exp 1) ≤ d) (hk : 0 < k) :
    ∃ τ : ℕ, sourceGraphTerminalScale n d < (sourceGraphRankSequence C n d k τ : ℝ) ∧
      (∀ j < τ, (sourceGraphRankSequence C n d k j : ℝ) ≤ sourceGraphTerminalScale n d) ∧
        (τ : ℝ) ≤ (4 * C + 2) * Real.log (n / k) ^ 4 := by
  have hOne : 1 ≤ d := by linarith [Real.add_one_le_exp (Real.exp 1), Real.exp_pos 1]
  obtain ⟨hu, _, hLog⟩ := source_graph_terminal_range hn hd
  exact source_graph_growth_first_exit_bound hC hn hOne hk hu hLog

end CircularLaw
