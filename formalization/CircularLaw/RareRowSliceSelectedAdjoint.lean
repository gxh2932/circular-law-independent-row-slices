import CircularLaw.RareSmallBallTensorization
import CircularLaw.RowSliceSelectedAdjointSmallBall
import CircularLaw.LogarithmicNetCost

/-!
# Rare-coefficient adjoint small balls for exact fixed-degree selected rows

The Bernoulli comparator gives exp(-m*d/8) at squared image radius
t^2*m*d/72. Conditioning only the m selected rows costs a power of
sqrt(d), which is absorbed by that exponential for large degree.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology

namespace CircularLaw

theorem bernoulli_columns_rare_weighted_norm_small_ball {ι : Type*} [Fintype ι] {n : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hRare : (Fintype.card ι : ℝ) * p ≤ 1 / 2)
    (a : ι → ℂ) {t : ℝ} (ht : 0 < t) (hLarge : ∀ i, t ≤ ‖a i‖) (z : Fin n → ℂ) :
    (Measure.pi (fun _ : Fin n => bernoulliCubeLaw ι p hp)).real
      {x | (∑ j, ‖(∑ i, weightedBernoulliValue (a i) (x j i)) - z j‖ ^ 2) ≤
        t ^ 2 * ((Fintype.card ι : ℝ) * p) * n / 72} ≤
      Real.exp (-((Fintype.card ι : ℝ) * p) * n / 8) := by
  let ν := bernoulliCubeLaw ι p hp
  let μ := Measure.pi (fun _ : Fin n => ν)
  let f := fun x : ι → Bool => ∑ i, weightedBernoulliValue (a i) (x i)
  apply finite_rare_small_ball_tensorization μ (fun j x => f (x j))
    (iIndepFun_pi (fun _ => (measurable_of_countable f).aemeasurable)) ht z
  intro j
  have hLaw := finite_law_event_real (measurable_pi_apply j)
    (measurePreserving_eval (fun _ : Fin n => ν) j).map_eq
    (fun x : ι → Bool => ‖f x - z j‖ ≤ t / 3)
  rw [hLaw]
  exact bernoulli_cube_rare_linear_form_small_ball p hp hRare a ht hLarge (z j)

theorem row_slice_selected_rows_rare_adjoint_small_ball {ι : Type*} [Fintype ι] {n d : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n)
    (hRare : (Fintype.card ι : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (a : ι → ℂ) {t : ℝ} (ht : 0 < t) (hLarge : ∀ i, t ≤ ‖a i‖) (z : Fin n → ℂ) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      (∑ j, ‖(∑ i, rowEntry (rows i) j * a i) - z j‖ ^ 2) ≤
        t ^ 2 * (Fintype.card ι : ℝ) * d / 72) ≤
      (4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ Fintype.card ι *
        Real.exp (-(Fintype.card ι : ℝ) * d / 8) := by
  have hn : 0 < n := by omega
  let p := rowBernoulliParameter n d
  let hp := rowBernoulliParameter_le_one hn (show d ≤ n by omega)
  let E := fun x : ι → Fin n → Bool =>
    (∑ j, ‖(∑ i, weightedBernoulliValue (a i) (x i j)) - z j‖ ^ 2) ≤
      t ^ 2 * (Fintype.card ι : ℝ) * d / 72
  have hTransfer := bernoulli_rows_slice_event_transfer_sqrt (ι := ι) hd (by omega : d ≤ n) E
  have hEntry : ∀ (s : RowSlice n d) (j : Fin n) (v : ℂ),
      weightedBernoulliValue v (rowSliceBoolRow s j) = rowEntry s j * v := by
    intro s j v
    by_cases hj : j ∈ s.val <;> simp [weightedBernoulliValue, rowSliceBoolRow, rowEntry, hj]
  simp only [E, hEntry] at hTransfer
  apply hTransfer.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hMap := bernoulli_rows_columns_map (ι := ι) (κ := Fin n) p hp
  have hEvent := finite_law_event_real (measurable_of_countable Function.swap) hMap
    (fun x : Fin n → ι → Bool =>
      (∑ j, ‖(∑ i, weightedBernoulliValue (a i) (x j i)) - z j‖ ^ 2) ≤
        t ^ 2 * (Fintype.card ι : ℝ) * d / 72)
  rw [hEvent]
  have hpCoe : (p : ℝ) = (d : ℝ) / n := rowBernoulliParameter_coe n d
  have hProbability := bernoulli_columns_rare_weighted_norm_small_ball p hp
    (by simpa only [hpCoe] using hRare) a ht hLarge z
  have hCancel : ((Fintype.card ι : ℝ) * (p : ℝ)) * n = (Fintype.card ι : ℝ) * d := by
    rw [hpCoe]
    field_simp
  have hThreshold : t ^ 2 * ((Fintype.card ι : ℝ) * (p : ℝ)) * n / 72 =
      t ^ 2 * (Fintype.card ι : ℝ) * d / 72 := by rw [mul_assoc, hCancel]; ring
  rw [hThreshold] at hProbability
  convert hProbability using 1
  congr 1
  nlinarith [hCancel]

theorem rare_row_slice_conditioning_cost_absorbed {d m : ℕ} (hd : 0 < d)
    (hCost : Real.log (4 * Real.exp 1 ^ 2 * Real.sqrt d) ≤ (d : ℝ) / 16) :
    (4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ m * Real.exp (-(m : ℝ) * d / 8) ≤
      Real.exp (-(m : ℝ) * d / 16) := by
  have hBase : 0 < 4 * Real.exp 1 ^ 2 * Real.sqrt d := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  rw [show (4 * Real.exp 1 ^ 2 * Real.sqrt d) ^ m =
      Real.exp ((m : ℝ) * Real.log (4 * Real.exp 1 ^ 2 * Real.sqrt d)) by
    rw [Real.exp_nat_mul, Real.exp_log hBase], ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hScaled := mul_le_mul_of_nonneg_left hCost (Nat.cast_nonneg (α := ℝ) m)
  nlinarith

theorem eventually_rare_row_slice_conditioning_cost :
    ∀ᶠ d : ℕ in atTop, 0 < d ∧
      Real.log (4 * Real.exp 1 ^ 2 * Real.sqrt d) ≤ (d : ℝ) / 16 := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1 / 16) (Real.log 4 + 2) (1 / 2) (by norm_num)]
      with d hd hCost
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  refine ⟨by omega, ?_⟩
  rw [Real.log_mul (by positivity : (4 : ℝ) * Real.exp 1 ^ 2 ≠ 0) hRoot.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : Real.exp 1 ^ 2 ≠ 0),
    Real.log_pow, Real.log_exp, Real.log_sqrt hdR.le]
  norm_num at hCost ⊢
  linarith

theorem row_slice_selected_rows_rare_adjoint_decay {ι : Type*} [Fintype ι] {n d : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n)
    (hRare : (Fintype.card ι : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (hCost : Real.log (4 * Real.exp 1 ^ 2 * Real.sqrt d) ≤ (d : ℝ) / 16)
    (a : ι → ℂ) {t : ℝ} (ht : 0 < t) (hLarge : ∀ i, t ≤ ‖a i‖) (z : Fin n → ℂ) :
    uniformProbability (fun rows : ι → RowSlice n d =>
      (∑ j, ‖(∑ i, rowEntry (rows i) j * a i) - z j‖ ^ 2) ≤
        t ^ 2 * (Fintype.card ι : ℝ) * d / 72) ≤
      Real.exp (-(Fintype.card ι : ℝ) * d / 16) :=
  (row_slice_selected_rows_rare_adjoint_small_ball hd hDegree hRare a ht hLarge z).trans
    (rare_row_slice_conditioning_cost_absorbed hd hCost)

end CircularLaw
