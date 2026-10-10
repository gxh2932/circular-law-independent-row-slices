import CircularLaw.FiniteProductFibers

/-!
# Many independent small-ball events

The coordinate events may have different laws. Their actual uniform
product law gives the Laplace transform of the failure count and an
exponential bound when at least seven eighths of the events occur.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def coordinateEventCount {ι : Type*} [Fintype ι] {α : ι → Type*}
    (E : ∀ i, α i → Prop) (x : ∀ i, α i) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => E i (x i))).card

theorem coordinateEventCount_cast {ι : Type*} [Fintype ι] {α : ι → Type*}
    (E : ∀ i, α i → Prop) (x : ∀ i, α i) :
    (coordinateEventCount E x : ℝ) = ∑ i, if E i (x i) then (1 : ℝ) else 0 := by
  classical
  simp only [coordinateEventCount, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem coordinateEventCount_compl {ι : Type*} [Fintype ι] {α : ι → Type*}
    (E : ∀ i, α i → Prop) (x : ∀ i, α i) :
    coordinateEventCount E x + coordinateEventCount (fun i a => ¬E i a) x = Fintype.card ι := by
  classical
  simp only [coordinateEventCount]
  convert (Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i => E i (x i))).trans Finset.card_univ using 1
  congr 1
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem coordinate_failure_laplace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (E : ∀ i, α i → Prop) :
    finiteMean (fun x : ∀ i, α i =>
      Real.exp (-Real.log 2 * coordinateEventCount (fun i a => ¬E i a) x)) =
        ∏ i, (1 - (1 - uniformProbability (E i)) / 2) := by
  classical
  have hProduct (x : ∀ i, α i) :
      Real.exp (-Real.log 2 * coordinateEventCount (fun i a => ¬E i a) x) =
        ∏ i, (1 - (if E i (x i) then (0 : ℝ) else 1) / 2) := by
    rw [coordinateEventCount_cast, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : E i (x i)
    · simp [hi]
    · simp only [hi, not_false_eq_true, ↓reduceIte, mul_one, Real.exp_neg,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
  simp_rw [hProduct]
  rw [finiteMean_pi_prod (fun i (a : α i) => 1 - (if E i a then (0 : ℝ) else 1) / 2)]
  apply Finset.prod_congr rfl
  intro i _
  have hIndicator (a : α i) : (if E i a then (0 : ℝ) else 1) =
      1 - (if E i a then (1 : ℝ) else 0) := by
    by_cases h : E i a <;> simp [h]
  simp_rw [hIndicator]
  simp_rw [div_eq_mul_inv]
  rw [finiteMean_sub, finiteMean_const, finiteMean_mul_const, finiteMean_sub,
    finiteMean_const, finiteMean_indicator]

def witnessHalfRate : ℝ := (2 - Real.log 2) / 8

theorem witnessHalfRate_pos : 0 < witnessHalfRate := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  unfold witnessHalfRate
  linarith

theorem independent_many_events_half {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (E : ∀ i, α i → Prop) (hHalf : ∀ i, uniformProbability (E i) ≤ 1 / 2) :
    uniformProbability (fun x : ∀ i, α i =>
      (7 / 8 : ℝ) * Fintype.card ι ≤ coordinateEventCount E x) ≤
        Real.exp (-witnessHalfRate * Fintype.card ι) := by
  let f := fun x : ∀ i, α i => Real.exp (-Real.log 2 * coordinateEventCount (fun i a => ¬E i a) x)
  let a := Real.exp (-Real.log 2 * ((Fintype.card ι : ℝ) / 8))
  have ha : 0 < a := Real.exp_pos _
  have hThreshold (x : ∀ i, α i)
      (hx : (7 / 8 : ℝ) * Fintype.card ι ≤ coordinateEventCount E x) : a ≤ f x := by
    have hCount := coordinateEventCount_compl E x
    have hReal : (coordinateEventCount E x : ℝ) +
        coordinateEventCount (fun i a => ¬E i a) x = Fintype.card ι := by exact_mod_cast hCount
    apply Real.exp_le_exp.mpr
    dsimp only [a, f]
    have hLog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    nlinarith
  have hMean : finiteMean f ≤ Real.exp (-(Fintype.card ι : ℝ) / 4) := by
    rw [show finiteMean f = ∏ i, (1 - (1 - uniformProbability (E i)) / 2) from coordinate_failure_laplace E]
    calc
      _ ≤ ∏ _i : ι, Real.exp (-1 / 4) := by
        apply Finset.prod_le_prod
        · intro i _
          linarith [uniformProbability_nonneg (E i)]
        · intro i _
          have h := Real.add_one_le_exp (-1 / 4 : ℝ)
          linarith [hHalf i]
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
        congr 1
        ring
  have hMark := finite_uniform_markov
    (fun x : ∀ i, α i => (7 / 8 : ℝ) * Fintype.card ι ≤ coordinateEventCount E x)
    f ha (fun _ => (Real.exp_pos _).le) hThreshold
  exact hMark.trans ((div_le_div_of_nonneg_right hMean ha.le).trans_eq (by
    dsimp only [a, witnessHalfRate]
    rw [← Real.exp_sub]
    congr 1
    ring))

end CircularLaw
