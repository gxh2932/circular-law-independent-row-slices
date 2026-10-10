import CircularLaw.WitnessNorm

/-!
# Logarithmic independent-event and Euclidean norm bounds

For coordinate probabilities bounded by `p <= 1/2`, the probability that
seven eighths of the events occur decays as `exp(-c*N*log(1/p))`.
This is the binomial estimate used for the large equal-block regime.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem coordinate_success_laplace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (E : ∀ i, α i → Prop) (t : ℝ) :
    finiteMean (fun x : ∀ i, α i => Real.exp (t * coordinateEventCount E x)) =
      ∏ i, (1 + uniformProbability (E i) * (Real.exp t - 1)) := by
  have hProduct (x : ∀ i, α i) :
      Real.exp (t * coordinateEventCount E x) =
        ∏ i, (1 + (if E i (x i) then (1 : ℝ) else 0) * (Real.exp t - 1)) := by
    rw [coordinateEventCount_cast, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : E i (x i) <;> simp [hi]
  simp_rw [hProduct]
  rw [finiteMean_pi_prod
    (fun i (a : α i) => 1 + (if E i a then (1 : ℝ) else 0) * (Real.exp t - 1))]
  apply Finset.prod_congr rfl
  intro i _
  rw [finiteMean_add, finiteMean_const, finiteMean_mul_const, finiteMean_indicator]

theorem log_four_eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

theorem independent_many_events_quarter {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (E : ∀ i, α i → Prop) {p : ℝ} (hp : 0 < p) (hpQuarter : p ≤ 1 / 4)
    (hProb : ∀ i, uniformProbability (E i) ≤ p) :
    uniformProbability (fun x : ∀ i, α i =>
      (7 / 8 : ℝ) * Fintype.card ι ≤ coordinateEventCount E x) ≤
        Real.exp (-(3 / 8 : ℝ) * Fintype.card ι * Real.log (1 / p)) := by
  let t := Real.log (1 / p)
  have hInv : (4 : ℝ) ≤ 1 / p := (le_div_iff₀ hp).mpr (by linarith)
  have htFour : 2 * Real.log 2 ≤ t := by
    exact log_four_eq ▸ Real.log_le_log (by norm_num) hInv
  have ht : 0 ≤ t := by
    have hLog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  have hExp : Real.exp t = 1 / p := Real.exp_log (div_pos (by norm_num) hp)
  have hExpOne : 0 ≤ Real.exp t - 1 := by rw [hExp]; linarith
  let f := fun x : ∀ i, α i => Real.exp (t * coordinateEventCount E x)
  let a := Real.exp (t * ((7 / 8 : ℝ) * Fintype.card ι))
  have ha : 0 < a := Real.exp_pos _
  have hMean : finiteMean f ≤ Real.exp (Real.log 2 * Fintype.card ι) := by
    rw [show finiteMean f = ∏ i, (1 + uniformProbability (E i) * (Real.exp t - 1)) from
      coordinate_success_laplace E t]
    calc
      _ ≤ ∏ _i : ι, (2 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _
          exact add_nonneg (by norm_num)
            (mul_nonneg (uniformProbability_nonneg (E i)) hExpOne)
        · intro i _
          have hTerm := mul_le_mul_of_nonneg_right (hProb i) hExpOne
          rw [hExp] at hTerm ⊢
          have hCancel : p * (1 / p - 1) = 1 - p := by field_simp
          rw [hCancel] at hTerm
          linarith
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ]
        calc
          _ = Real.exp ((Fintype.card ι : ℝ) * Real.log 2) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          _ = _ := by congr 1; ring
  have hMark := finite_uniform_markov
    (fun x : ∀ i, α i => (7 / 8 : ℝ) * Fintype.card ι ≤ coordinateEventCount E x)
    f ha (fun _ => (Real.exp_pos _).le)
    (fun _ hx => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx ht))
  apply hMark.trans
  apply (div_le_div_of_nonneg_right hMean ha.le).trans
  dsimp only [a]
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  nlinarith

def witnessLogRate : ℝ := min (3 / 8) (witnessHalfRate / (2 * Real.log 2))

theorem witnessLogRate_pos : 0 < witnessLogRate := by
  exact lt_min (by norm_num)
    (div_pos witnessHalfRate_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num))))

theorem independent_many_events_log {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (E : ∀ i, α i → Prop) {p : ℝ} (hp : 0 < p) (hpHalf : p ≤ 1 / 2)
    (hProb : ∀ i, uniformProbability (E i) ≤ p) :
    uniformProbability (fun x : ∀ i, α i =>
      (7 / 8 : ℝ) * Fintype.card ι ≤ coordinateEventCount E x) ≤
        Real.exp (-witnessLogRate * Fintype.card ι * Real.log (1 / p)) := by
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hLog : 0 ≤ Real.log (1 / p) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hp).mpr (by linarith)
  by_cases hQuarter : p ≤ 1 / 4
  · apply (independent_many_events_quarter E hp hQuarter hProb).trans
    apply Real.exp_le_exp.mpr
    have hRate := min_le_left (3 / 8 : ℝ) (witnessHalfRate / (2 * Real.log 2))
    change witnessLogRate ≤ (3 / 8 : ℝ) at hRate
    nlinarith [mul_nonneg hN hLog]
  · apply (independent_many_events_half E (fun i => (hProb i).trans hpHalf)).trans
    apply Real.exp_le_exp.mpr
    have hLogTwo : 0 < 2 * Real.log 2 :=
      mul_pos (by norm_num) (Real.log_pos (by norm_num))
    have hLogFour : Real.log (1 / p) ≤ 2 * Real.log 2 := by
      rw [← log_four_eq]
      apply Real.log_le_log (div_pos (by norm_num) hp)
      exact (div_le_iff₀ hp).mpr (by linarith [lt_of_not_ge hQuarter])
    have hRate : witnessLogRate * (2 * Real.log 2) ≤ witnessHalfRate := by
      exact (le_div_iff₀ hLogTwo).mp (min_le_right _ _)
    have hRateLog : witnessLogRate * Real.log (1 / p) ≤ witnessHalfRate :=
      (mul_le_mul_of_nonneg_left hLogFour witnessLogRate_pos.le).trans hRate
    nlinarith

theorem independent_norm_small_ball_log {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (Y : ∀ i, α i → ℂ) {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hpHalf : p ≤ 1 / 2)
    (hProb : ∀ i, uniformProbability (fun a : α i => ‖Y i a‖ < r) ≤ p) :
    uniformProbability (fun x : ∀ i, α i =>
      (∑ i, ‖Y i (x i)‖ ^ 2) ≤ r ^ 2 * (Fintype.card ι : ℝ) / 8) ≤
        Real.exp (-witnessLogRate * Fintype.card ι * Real.log (1 / p)) := by
  apply (uniformProbability_mono ?_).trans
    (independent_many_events_log (fun i a => ‖Y i a‖ < r) hp hpHalf hProb)
  intro x hx
  exact norm_sq_small_implies_many_small (fun i => Y i (x i)) hr hx

end CircularLaw
