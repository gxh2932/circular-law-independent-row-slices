import CircularLaw.Conditioning

/-!
# With-replacement occupancy tails

Independent uniform sampling gives binomial counts for each part of a row
profile. This file proves the Laplace transform and the multiplicative
lower-tail bound used to control under-visited large parts in Section 3.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def trialCount {α : Type*} (P : α → Prop) {d : ℕ} (samples : Fin d → α) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => P (samples i))).card

theorem trialCount_cast {α : Type*} (P : α → Prop) [DecidablePred P]
    {d : ℕ} (samples : Fin d → α) :
    (trialCount P samples : ℝ) = ∑ i : Fin d, if P (samples i) then (1 : ℝ) else 0 := by
  classical
  simp only [trialCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]

theorem trial_laplace {α : Type*} [Fintype α] [Nonempty α] (P : α → Prop) (d : ℕ) :
    finiteMean (fun samples : Fin d → α => Real.exp (-Real.log 2 * trialCount P samples)) =
      (1 - uniformProbability P / 2) ^ d := by
  classical
  have he (samples : Fin d → α) : Real.exp (-Real.log 2 * trialCount P samples) =
      ∏ i, (1 - (if P (samples i) then (1 : ℝ) else 0) / 2) := by
    rw [trialCount_cast, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : P (samples i)
    · simp only [if_pos hi, mul_one, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    · simp [hi]
  simp_rw [he]
  rw [finiteMean_pi_prod (fun _ : Fin d =>
    fun a : α => 1 - (if P a then (1 : ℝ) else 0) / 2)]
  have hmean : finiteMean (fun a : α => 1 - (if P a then (1 : ℝ) else 0) / 2) =
      1 - uniformProbability P / 2 := by
    simp_rw [div_eq_mul_inv]
    rw [finiteMean_sub, finiteMean_const, finiteMean_mul_const, finiteMean_indicator]
  simp only [hmean, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def binomialHalfRate : ℝ := (1 - Real.log 2) / 2

theorem binomialHalfRate_pos : 0 < binomialHalfRate := by
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  unfold binomialHalfRate
  linarith

/-- A multiplicative Chernoff bound derived from independence, with
explicit absolute rate `(1-log 2)/2`. -/
theorem binomial_lower_tail_half {α : Type*} [Fintype α] [Nonempty α]
    (P : α → Prop) (d : ℕ) :
    uniformProbability (fun samples : Fin d → α =>
      (trialCount P samples : ℝ) < (d : ℝ) * uniformProbability P / 2) ≤
        Real.exp (-binomialHalfRate * d * uniformProbability P) := by
  let f : (Fin d → α) → ℝ := fun samples => Real.exp (-Real.log 2 * trialCount P samples)
  let a : ℝ := Real.exp (-Real.log 2 * ((d : ℝ) * uniformProbability P / 2))
  have ha : 0 < a := Real.exp_pos _
  have hthreshold (samples : Fin d → α)
      (h : (trialCount P samples : ℝ) < (d : ℝ) * uniformProbability P / 2) : a ≤ f samples := by
    apply Real.exp_le_exp.mpr
    dsimp [a, f]
    have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith
  have hmgf : finiteMean f ≤ Real.exp (-(d : ℝ) * uniformProbability P / 2) := by
    rw [show finiteMean f = (1 - uniformProbability P / 2) ^ d from trial_laplace P d]
    have hbase : 1 - uniformProbability P / 2 ≤ Real.exp (-uniformProbability P / 2) := by
      have h := Real.add_one_le_exp (-uniformProbability P / 2)
      linarith
    calc
      _ ≤ (Real.exp (-uniformProbability P / 2)) ^ d :=
        pow_le_pow_left₀ (by linarith [uniformProbability_le_one P]) hbase d
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hmark := finite_uniform_markov
    (fun samples : Fin d → α => (trialCount P samples : ℝ) < (d : ℝ) * uniformProbability P / 2)
    f ha (fun _ => (Real.exp_pos _).le) hthreshold
  calc
    _ ≤ finiteMean f / a := hmark
    _ ≤ Real.exp (-(d : ℝ) * uniformProbability P / 2) / a :=
      div_le_div_of_nonneg_right hmgf ha.le
    _ = _ := by
      dsimp [a, binomialHalfRate]
      rw [← Real.exp_sub]
      congr 1; ring

theorem uniformProbability_finset_exists_le {α ι : Type*} [Fintype α]
    (T : Finset ι) (E : ι → α → Prop) :
    uniformProbability (fun a => ∃ i ∈ T, E i a) ≤ ∑ i ∈ T, uniformProbability (E i) := by
  classical
  rw [← finiteMean_indicator]
  calc
    _ ≤ finiteMean (fun a : α => ∑ i ∈ T, if E i a then (1 : ℝ) else 0) := by
      apply finiteMean_mono
      intro a
      by_cases h : ∃ i ∈ T, E i a
      · rw [if_pos h]
        rcases h with ⟨i, hi, hia⟩
        have hs := Finset.single_le_sum
          (f := fun j => if E j a then (1 : ℝ) else 0) (fun _ _ => by positivity) hi
        simpa only [if_pos hia] using hs
      · rw [if_neg h]
        exact Finset.sum_nonneg (fun _ _ => by positivity)
    _ = _ := by
      rw [finiteMean_finset_sum]
      simp only [finiteMean_indicator]

/-- The union bound for under-visited large profile parts. No independence
between the part counts is assumed: only the independent sample law is used. -/
theorem profile_good_failure_bound {α ι : Type*} [Fintype α] [Nonempty α]
    (P : ι → α → Prop) (T : Finset ι) (d : ℕ) {r : ℝ}
    (hlarge : ∀ q ∈ T, r ≤ uniformProbability (P q)) :
    uniformProbability (fun samples : Fin d → α => ∃ q ∈ T,
      (trialCount (P q) samples : ℝ) < (d : ℝ) * uniformProbability (P q) / 2) ≤
        (T.card : ℝ) * Real.exp (-binomialHalfRate * d * r) := by
  apply le_trans (uniformProbability_finset_exists_le T _)
  calc
    _ ≤ ∑ _q ∈ T, Real.exp (-binomialHalfRate * d * r) := by
      apply Finset.sum_le_sum
      intro q hq
      apply le_trans (binomial_lower_tail_half (P q) d)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hlarge q hq)
        (by simpa only [neg_mul] using
          (neg_nonpos.mpr (mul_nonneg binomialHalfRate_pos.le (Nat.cast_nonneg d))))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem disjoint_parts_probability_sum_le_one {α ι : Type*} [Fintype α] [Nonempty α]
    (P : ι → α → Prop) (T : Finset ι)
    (hunique : ∀ a i, i ∈ T → ∀ j, j ∈ T → P i a → P j a → i = j) :
    (∑ q ∈ T, uniformProbability (P q)) ≤ 1 := by
  classical
  calc
    _ = finiteMean (fun a : α => ∑ q ∈ T, if P q a then (1 : ℝ) else 0) := by
      rw [finiteMean_finset_sum]
      simp only [finiteMean_indicator]
    _ ≤ finiteMean (fun _ : α => (1 : ℝ)) := by
      apply finiteMean_mono
      intro a
      have hc : (T.filter (fun q => P q a)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro i hi j hj
        rcases Finset.mem_filter.mp hi with ⟨hiT, hia⟩
        rcases Finset.mem_filter.mp hj with ⟨hjT, hja⟩
        exact hunique a i hiT j hjT hia hja
      have hc' : ((T.filter (fun q => P q a)).card : ℝ) ≤ 1 := by exact_mod_cast hc
      simpa only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hc'
    _ = 1 := finiteMean_const 1

theorem large_parts_card_le {α ι : Type*} [Fintype α] [Nonempty α]
    (P : ι → α → Prop) (T : Finset ι) {r : ℝ} (hr : 0 < r)
    (hunique : ∀ a i, i ∈ T → ∀ j, j ∈ T → P i a → P j a → i = j)
    (hlarge : ∀ q ∈ T, r ≤ uniformProbability (P q)) :
    (T.card : ℝ) ≤ 1 / r := by
  apply (le_div_iff₀ hr).mpr
  calc
    _ = ∑ _q ∈ T, r := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ q ∈ T, uniformProbability (P q) := Finset.sum_le_sum hlarge
    _ ≤ 1 := disjoint_parts_probability_sum_le_one P T hunique

/-- The explicit Section 3 large-profile failure bound, with the genuine
`d^(1/3)` prefactor and `d^(2/3)` exponential scale. -/
theorem profile_good_failure_power_bound {α ι : Type*} [Fintype α] [Nonempty α]
    (P : ι → α → Prop) (T : Finset ι) {d : ℕ} (hd : 0 < d)
    (hunique : ∀ a i, i ∈ T → ∀ j, j ∈ T → P i a → P j a → i = j)
    (hlarge : ∀ q ∈ T, Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤ uniformProbability (P q)) :
    uniformProbability (fun samples : Fin d → α => ∃ q ∈ T,
      (trialCount (P q) samples : ℝ) < (d : ℝ) * uniformProbability (P q) / 2) ≤
        Real.rpow (d : ℝ) (1 / 3 : ℝ) *
          Real.exp (-binomialHalfRate * Real.rpow (d : ℝ) (2 / 3 : ℝ)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hcard := large_parts_card_le P T (r := Real.rpow (d : ℝ) (-1 / 3 : ℝ))
    (Real.rpow_pos_of_pos hd' (-1 / 3 : ℝ)) hunique hlarge
  have hinv : 1 / Real.rpow (d : ℝ) (-1 / 3 : ℝ) = Real.rpow (d : ℝ) (1 / 3 : ℝ) := by
    simp only [Real.rpow_eq_pow]
    rw [show (-1 / 3 : ℝ) = -(1 / 3 : ℝ) by ring,
      Real.rpow_neg hd'.le (1 / 3 : ℝ), one_div, inv_inv]
  rw [hinv] at hcard
  have hpow : (d : ℝ) * Real.rpow (d : ℝ) (-1 / 3 : ℝ) =
      Real.rpow (d : ℝ) (2 / 3 : ℝ) := by
    simp only [Real.rpow_eq_pow]
    calc
      _ = (d : ℝ) ^ (1 : ℝ) * (d : ℝ) ^ (-1 / 3 : ℝ) := by rw [Real.rpow_one]
      _ = (d : ℝ) ^ ((1 : ℝ) + (-1 / 3 : ℝ)) := (Real.rpow_add hd' _ _).symm
      _ = _ := by norm_num
  have h := profile_good_failure_bound P T d hlarge
  rw [show -binomialHalfRate * (d : ℝ) * Real.rpow (d : ℝ) (-1 / 3 : ℝ) =
      -binomialHalfRate * Real.rpow (d : ℝ) (2 / 3 : ℝ) by rw [mul_assoc, hpow]] at h
  exact h.trans (mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _))

theorem multinomial_large_parts_failure {α ι : Type*} [Fintype α] [Nonempty α]
    (part : α → ι) (T : Finset ι) {d : ℕ} (hd : 0 < d)
    (hlarge : ∀ q ∈ T, Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤
      uniformProbability (fun a => part a = q)) :
    uniformProbability (fun samples : Fin d → α => ∃ q ∈ T,
      (trialCount (fun a => part a = q) samples : ℝ) <
        (d : ℝ) * uniformProbability (fun a => part a = q) / 2) ≤
      Real.rpow (d : ℝ) (1 / 3 : ℝ) *
        Real.exp (-binomialHalfRate * Real.rpow (d : ℝ) (2 / 3 : ℝ)) :=
  profile_good_failure_power_bound (fun q a => part a = q) T hd
    (fun _ _ _ _ _ hi hj => hi.symm.trans hj) hlarge

/-- The polynomial prefactor in the profile failure probability can be
absorbed into half the exponential rate for all sufficiently large degrees. -/
theorem eventually_profile_prefactor_absorbed :
    ∀ᶠ d : ℕ in Filter.atTop,
      Real.rpow (d : ℝ) (1 / 3 : ℝ) *
        Real.exp (-binomialHalfRate * Real.rpow (d : ℝ) (2 / 3 : ℝ)) ≤
          Real.exp (-(binomialHalfRate / 2) * Real.rpow (d : ℝ) (2 / 3 : ℝ)) := by
  have hlim := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun d : ℕ => (d : ℝ)) Filter.atTop Filter.atTop)
  have hsmall : ∀ᶠ d : ℕ in Filter.atTop,
      Real.log (d : ℝ) / Real.rpow (d : ℝ) (2 / 3 : ℝ) < 3 * binomialHalfRate / 2 :=
    hlim.eventually (gt_mem_nhds (by nlinarith [binomialHalfRate_pos] :
      (0 : ℝ) < 3 * binomialHalfRate / 2))
  filter_upwards [hsmall, Filter.eventually_ge_atTop 1] with d hd hdone
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlt := (div_lt_iff₀ (Real.rpow_pos_of_pos hdpos (2 / 3 : ℝ))).mp hd
  simp only [Real.rpow_eq_pow] at hlt ⊢
  rw [Real.rpow_def_of_pos hdpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end CircularLaw
