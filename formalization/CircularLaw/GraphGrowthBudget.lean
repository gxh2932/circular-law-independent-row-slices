import CircularLaw.GraphCoordinateGap

/-!
# The actual graph growth function supplies the middle-support budget

The ceiling in the source growth function is retained. A fixed explicit
constant, depending only on the column-degree constant, makes the middle
set of size g-1 small enough. No middle-support budget is assumed here.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def sourceGraphExpansion (n d x : ℝ) : ℝ := d * x / Real.log (n / x) ^ 2

def sourceGraphGrowthBase (C n d x : ℝ) : ℝ :=
  sourceGraphExpansion n d x / (C * (d + Real.log (n / x)))

def sourceGraphGrowth (C n d x : ℝ) : ℕ := Nat.ceil (sourceGraphGrowthBase C n d x)

def graphGrowthConstant (K : ℝ) : ℝ := (64 * (K + 1)) ^ 2

def MatrixColumnDegreeBudget {ρ ι : Type*} [Fintype ρ]
    (A : Matrix ρ ι ℂ) (K n d : ℝ) : Prop :=
  ∀ T : Finset ι, (∑ j ∈ T, ((matrixColumnSupport A j).card : ℝ)) ≤
    K * T.card * (d + Real.log (n / T.card))

theorem graph_growth_constant_ge_one {K : ℝ} (hK : 0 ≤ K) :
    1 ≤ graphGrowthConstant K := by
  unfold graphGrowthConstant
  nlinarith

theorem graph_growth_constant_log_budget {K : ℝ} (hK : 0 ≤ K) :
    4 * K * (5 + Real.log (graphGrowthConstant K)) ≤ graphGrowthConstant K := by
  have hBase : 0 < 64 * (K + 1) := by positivity
  have hLog := Real.log_le_sub_one_of_pos hBase
  rw [graphGrowthConstant, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith [mul_nonneg hK (sub_nonneg.mpr hLog)]

theorem source_graph_growth_base_pos {C n d x : ℝ}
    (hC : 0 < C) (hd : 0 < d) (hx : 0 < x)
    (hLog : 1 ≤ Real.log (n / x)) : 0 < sourceGraphGrowthBase C n d x := by
  have hL : 0 < Real.log (n / x) := by linarith
  unfold sourceGraphGrowthBase sourceGraphExpansion
  positivity

theorem source_graph_growth_pos {C n d x : ℝ}
    (hC : 0 < C) (hd : 0 < d) (hx : 0 < x)
    (hLog : 1 ≤ Real.log (n / x)) : 0 < sourceGraphGrowth C n d x :=
  Nat.ceil_pos.mpr (source_graph_growth_base_pos hC hd hx hLog)

theorem source_graph_growth_middle_le_base {C n d x : ℝ}
    (hC : 0 < C) (hd : 0 < d) (hx : 0 < x)
    (hLog : 1 ≤ Real.log (n / x)) :
    ((sourceGraphGrowth C n d x - 1 : ℕ) : ℝ) ≤ sourceGraphGrowthBase C n d x := by
  have hg := source_graph_growth_pos hC hd hx hLog
  exact ((Nat.ceil_eq_iff (Nat.ne_of_gt hg)).mp
    (rfl : Nat.ceil (sourceGraphGrowthBase C n d x) = sourceGraphGrowth C n d x)).1.le

theorem logarithmic_degree_budget_mono {n d s y : ℝ}
    (hn : 0 < n) (hd : 0 ≤ d) (hs : 0 < s) (hy : 0 < y) (hsy : s ≤ y)
    (hLog : 0 ≤ Real.log (n / y)) :
    s * (d + Real.log (n / s) + 1) ≤ y * (d + Real.log (n / y) + 1) := by
  have hLogEq : Real.log (n / s) = Real.log (n / y) + Real.log (y / s) := by
    rw [Real.log_div hn.ne' hs.ne', Real.log_div hn.ne' hy.ne', Real.log_div hy.ne' hs.ne']
    ring
  have hLogBound := Real.log_le_sub_one_of_pos (div_pos hy hs)
  have hMul := mul_le_mul_of_nonneg_left hLogBound hs.le
  have hCancel : s * (y / s - 1) = y - s := by field_simp
  rw [hCancel] at hMul
  rw [hLogEq]
  nlinarith [mul_nonneg (sub_nonneg.mpr hsy) (add_nonneg hd hLog)]

theorem source_graph_growth_base_le_coordinate {C n d x : ℝ}
    (hC : 1 ≤ C) (hd : 1 ≤ d) (hx : 0 < x)
    (hLog : 1 ≤ Real.log (n / x)) : sourceGraphGrowthBase C n d x ≤ x := by
  have hCp : 0 < C := by linarith
  have hdp : 0 < d := by linarith
  have hLp : 0 < Real.log (n / x) := by linarith
  have hSquare : 1 ≤ Real.log (n / x) ^ 2 := by nlinarith
  have hDen : d ≤ Real.log (n / x) ^ 2 * (C * (d + Real.log (n / x))) := by
    calc
      d ≤ d + Real.log (n / x) := by linarith
      _ ≤ C * (d + Real.log (n / x)) :=
        le_mul_of_one_le_left (by positivity) hC
      _ ≤ Real.log (n / x) ^ 2 * (C * (d + Real.log (n / x))) :=
        le_mul_of_one_le_left (by positivity) hSquare
  unfold sourceGraphGrowthBase sourceGraphExpansion
  rw [div_div]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hDen hx.le]

theorem source_graph_growth_base_degree_bound {C n d x : ℝ}
    (hC : 1 ≤ C) (hn : 0 < n) (hd : 1 ≤ d) (hx : 0 < x)
    (hLog : 1 ≤ Real.log (n / x)) :
    sourceGraphGrowthBase C n d x *
      (d + Real.log (n / sourceGraphGrowthBase C n d x) + 1) ≤
        sourceGraphExpansion n d x * (5 + Real.log C) / C := by
  let L := Real.log (n / x)
  let y := sourceGraphGrowthBase C n d x
  have hCp : 0 < C := by linarith
  have hdp : 0 < d := by linarith
  have hLp : 0 < L := by dsimp [L]; linarith
  have hyp : 0 < y := source_graph_growth_base_pos hCp hdp hx hLog
  have hLogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hLogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hRatio : (d + L) / d ≤ 1 + L := by
    apply (div_le_iff₀ hdp).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) hLp.le]
  have hLogRatio : Real.log ((d + L) / d) ≤ L := by
    have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0 < d + L) hdp)
    linarith
  have hLogEq : Real.log (n / y) = L + Real.log C + 2 * Real.log L +
      Real.log ((d + L) / d) := by
    change Real.log (n / y) = _
    have hLogY : Real.log y = Real.log d + Real.log x - 2 * Real.log L -
        Real.log C - Real.log (d + L) := by
      change Real.log ((d * x / L ^ 2) / (C * (d + L))) = _
      rw [Real.log_div (div_pos (mul_pos hdp hx) (pow_pos hLp 2)).ne'
        (mul_pos hCp (by positivity : 0 < d + L)).ne',
        Real.log_div (mul_pos hdp hx).ne' (pow_ne_zero 2 hLp.ne'),
        Real.log_mul hdp.ne' hx.ne', Real.log_pow,
        Real.log_mul hCp.ne' (by positivity : (d + L) ≠ 0)]
      ring
    rw [Real.log_div hn.ne' hyp.ne', hLogY,
      Real.log_div (by positivity : (d + L) ≠ 0) hdp.ne']
    have hLId : L = Real.log n - Real.log x := Real.log_div hn.ne' hx.ne'
    rw [hLId]
    ring
  have hDegree : d + Real.log (n / y) + 1 ≤ (5 + Real.log C) * (d + L) := by
    rw [hLogEq]
    nlinarith [mul_nonneg (add_nonneg hLogC (by norm_num : (0 : ℝ) ≤ 1))
      (sub_nonneg.mpr (show 1 ≤ d + L by linarith))]
  have hMul := mul_le_mul_of_nonneg_left hDegree hyp.le
  have hIdentity : y * ((5 + Real.log C) * (d + L)) =
      sourceGraphExpansion n d x * (5 + Real.log C) / C := by
    dsimp [y, sourceGraphGrowthBase, L]
    field_simp
  exact hMul.trans_eq hIdentity

theorem source_graph_middle_degree_bound {K n d x s : ℝ}
    (hK : 0 ≤ K) (hn : 0 < n) (hd : 1 ≤ d) (hx : 0 < x)
    (hLog : 1 ≤ Real.log (n / x)) (hs : 0 ≤ s)
    (hsSmall : s ≤ sourceGraphGrowthBase (graphGrowthConstant K) n d x) :
    K * s * (d + Real.log (n / s) + 1) ≤ sourceGraphExpansion n d x / 4 := by
  let C := graphGrowthConstant K
  let y := sourceGraphGrowthBase C n d x
  have hC : 1 ≤ C := graph_growth_constant_ge_one hK
  have hCp : 0 < C := by linarith
  have hdp : 0 < d := by linarith
  have hy : 0 < y := source_graph_growth_base_pos hCp hdp hx hLog
  have hB : 0 < sourceGraphExpansion n d x := by
    have hLp : 0 < Real.log (n / x) := by linarith
    unfold sourceGraphExpansion
    positivity
  by_cases hsZero : s = 0
  · simp only [hsZero, mul_zero, zero_mul]
    positivity
  have hsPos : 0 < s := lt_of_le_of_ne hs (Ne.symm hsZero)
  have hyx : y ≤ x := source_graph_growth_base_le_coordinate hC hd hx hLog
  have hLogY : 0 ≤ Real.log (n / y) := by
    have hRatio : n / x ≤ n / y := div_le_div_of_nonneg_left hn.le hy hyx
    have h := Real.log_le_log (div_pos hn hx) hRatio
    linarith
  have hMono := logarithmic_degree_budget_mono hn hdp.le hsPos hy hsSmall hLogY
  have hDegree := source_graph_growth_base_degree_bound hC hn hd hx hLog
  have hBig := graph_growth_constant_log_budget hK
  have hScaled := mul_le_mul_of_nonneg_left (hMono.trans hDegree) hK
  calc
    K * s * (d + Real.log (n / s) + 1) = K * (s * (d + Real.log (n / s) + 1)) := by ring
    _ ≤ K * (sourceGraphExpansion n d x * (5 + Real.log C) / C) := hScaled
    _ ≤ sourceGraphExpansion n d x / 4 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
      rw [show K * (sourceGraphExpansion n d x * (5 + Real.log C) / C) * 4 =
        (4 * K * (5 + Real.log C) * sourceGraphExpansion n d x) / C by ring]
      apply (div_le_iff₀ hCp).mpr
      have h := mul_le_mul_of_nonneg_right hBig hB.le
      simpa only [C, mul_comm] using h

end CircularLaw
