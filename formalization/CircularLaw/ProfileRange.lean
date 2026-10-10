import CircularLaw.ProfileEstimator
import CircularLaw.DegreeRates

/-!
# Profile ranges in the logarithmic degree regime

These proofs connect the actual truncated-weight definitions to the support
diameter needed by the max-weight lemma. The canonical decomposition's height
bound is recorded explicitly; no geometric decomposition theorem is assumed.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

theorem truncatedProfileWeight_bounds {α ι : Type*} [Fintype α] (P : RowProfile α ι)
    {d : ℕ} (hd : 0 < d) (q : ι) (hheight : P.height q ≤ Fintype.card α) :
    (P.height q : ℝ) / d ≤ truncatedProfileWeight P d q ∧
      truncatedProfileWeight P d q ≤ (Fintype.card α : ℝ) * Real.sqrt d := by
  classical
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hh : (0 : ℝ) < P.height q := by exact_mod_cast P.height_pos q
  have hhN : (P.height q : ℝ) ≤ Fintype.card α := by exact_mod_cast hheight
  have hp := rowProfile_mass_pos P q
  have hp1 : partMass P.part q ≤ 1 := uniformProbability_le_one _
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt d :=
    (Real.le_sqrt (by norm_num) hd'.le).mpr (by simpa using hd1)
  have hhdiv : (P.height q : ℝ) / d ≤ P.height q := div_le_self hh.le hd1
  have htop : (P.height q : ℝ) ≤ (Fintype.card α : ℝ) * Real.sqrt d := by
    calc
      _ ≤ (Fintype.card α : ℝ) := hhN
      _ ≤ _ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrt1
          (Nat.cast_nonneg (Fintype.card α) : (0 : ℝ) ≤ Fintype.card α)
  unfold truncatedProfileWeight
  by_cases hlarge : Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤ partMass P.part q
  · rw [if_pos hlarge]
    have hpow : 1 / (d : ℝ) ≤ Real.rpow (d : ℝ) (-1 / 3 : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num : (-1 : ℝ) ≤ -1 / 3)
      simpa only [Real.rpow_neg_one, one_div, Real.rpow_eq_pow] using h
    have hmass : 1 / (d : ℝ) ≤ partMass P.part q := hpow.trans hlarge
    by_cases hs : P.spread q = true
    · rw [if_pos hs]
      have hdp : 1 ≤ (d : ℝ) * partMass P.part q := by
        simpa only [mul_comm] using (div_le_iff₀ hd').mp hmass
      have hsq : (1 : ℝ) ≤ Real.sqrt ((d : ℝ) * partMass P.part q) :=
        (Real.le_sqrt (by norm_num) (mul_nonneg hd'.le hp.le)).mpr (by simpa using hdp)
      have hsqtop := Real.sqrt_le_sqrt (mul_le_of_le_one_right hd'.le hp1)
      constructor
      · exact hhdiv.trans (by nlinarith)
      · exact mul_le_mul hhN hsqtop (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
    · rw [if_neg hs]
      constructor
      · simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hmass hh.le
      · exact (mul_le_of_le_one_right hh.le hp1).trans htop
  · rw [if_neg hlarge]
    by_cases hs : P.spread q = true
    · rw [if_pos hs]
      exact ⟨hhdiv, htop⟩
    · rw [if_neg hs]
      exact ⟨le_rfl, hhdiv.trans htop⟩

theorem dyadicWeight_range_le {α : Type*} (w : α → ℝ) {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (hlower : ∀ a, 1 / (d : ℝ) ≤ w a)
    (hupper : ∀ a, w a ≤ (n : ℝ) * Real.sqrt d) (a b : α) :
    |dyadicWeight (w a) - dyadicWeight (w b)| ≤
      Real.logb 2 n + (3 / 2 : ℝ) * Real.logb 2 d + 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hw (a : α) : 0 < w a := lt_of_lt_of_le (one_div_pos.mpr hd') (hlower a)
  have hlowlog : Real.logb 2 (1 / (d : ℝ)) = -Real.logb 2 d := by
    rw [Real.logb_div one_ne_zero hd'.ne', Real.logb_one]
    ring
  have huplog : Real.logb 2 ((n : ℝ) * Real.sqrt d) =
      Real.logb 2 n + Real.logb 2 d / 2 := by
    rw [Real.logb_mul hn'.ne' (Real.sqrt_pos.mpr hd').ne']
    simp only [Real.logb, Real.log_sqrt hd'.le]
    ring
  have hbounds (a : α) : -Real.logb 2 d - 1 ≤ dyadicWeight (w a) ∧
      dyadicWeight (w a) ≤ Real.logb 2 n + Real.logb 2 d / 2 := by
    constructor
    · have hl := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
        (one_div_pos.mpr hd') (hw a)).mpr (hlower a)
      rw [hlowlog] at hl
      have hf := (Int.sub_one_lt_floor (Real.logb 2 (w a))).le
      change Real.logb 2 (w a) - 1 ≤ dyadicWeight (w a) at hf
      linarith
    · have hu := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
        (hw a) (mul_pos hn' (Real.sqrt_pos.mpr hd'))).mpr (hupper a)
      rw [huplog] at hu
      exact (Int.floor_le _).trans hu
  have ha := hbounds a
  have hb := hbounds b
  apply abs_le.mpr
  constructor <;> linarith

theorem truncatedProfileWeight_dyadic_range {n r d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (P : RowProfile (Fin n) (Fin r)) (hheight : ∀ q, P.height q ≤ n) (a b : Fin n) :
    |dyadicWeight (truncatedProfileWeight P d (P.part a)) -
      dyadicWeight (truncatedProfileWeight P d (P.part b))| ≤
        Real.logb 2 n + (3 / 2 : ℝ) * Real.logb 2 d + 2 := by
  apply dyadicWeight_range_le _ hn hd _ _ a b
  · intro j
    have h := (truncatedProfileWeight_bounds P hd (P.part j)
      (by simpa only [Fintype.card_fin] using hheight (P.part j))).1
    have hh : (1 : ℝ) ≤ P.height (P.part j) := by exact_mod_cast P.height_pos (P.part j)
    exact (div_le_div_of_nonneg_right hh (Nat.cast_nonneg d)).trans h
  · intro j
    simpa only [Fintype.card_fin] using
      (truncatedProfileWeight_bounds P hd (P.part j)
        (by simpa only [Fintype.card_fin] using hheight (P.part j))).2

/-- The weight-range hypothesis of the estimator bound is established from
the definitions under the paper's logarithmic lower bound. -/
theorem truncated_profile_range_le_degree {n r d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hdn : d ≤ n) (hlogn : 2 ≤ Real.log (n : ℝ)) (hlower : 96 * Real.log (n : ℝ) ≤ d)
    (P : RowProfile (Fin n) (Fin r)) (hheight : ∀ q, P.height q ≤ n) (a b : Fin n) :
    |dyadicWeight (truncatedProfileWeight P d (P.part a)) -
      dyadicWeight (truncatedProfileWeight P d (P.part b))| ≤ (d : ℝ) / 12 :=
  (truncatedProfileWeight_dyadic_range hn hd P hheight a b).trans
    (weight_range_le_degree hlogn hd hdn hlower)

theorem degree_tendsto_atTop_of_log_lower {C : ℝ} {d : ℕ → ℕ}
    (hC : 0 < C) (hlog : LogLowerBound C d) :
    Filter.Tendsto d Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro D
  have hlim := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)
  filter_upwards [hlog, hlim.eventually_ge_atTop ((D : ℝ) / C)] with n hn hlarge
  dsimp only [Function.comp_apply] at hlarge
  have hreal : (D : ℝ) ≤ d n := by
    have h := (div_le_iff₀ hC).mp hlarge
    nlinarith
  exact_mod_cast hreal

/-- The first averaged-profile conclusion holds eventually, uniformly over
every partition and its admissible heights, under the main theorem's degree
assumptions with logarithmic constant at least 96. In particular, the
support-diameter condition is a conclusion here, not an additional premise. -/
theorem eventually_averaged_profile_estimator {C : ℝ} {d : ℕ → ℕ}
    (hC : 96 ≤ C) (hlog : LogLowerBound C d) (hsparse : SparseDegrees d) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ hd : 2 ≤ d n, ∀ r : ℕ,
      ∀ P : RowProfile (Fin n) (Fin r), (∀ q, P.height q ≤ n) →
        finiteMean (fun samples : Fin (d n) → Fin n =>
          profileEstimator P.part (actualProfileWeight P samples) (by omega) samples) ≤
          4 * Real.exp (-averagedProfileRate *
            pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P (d n) (P.part a)))) *
              profileGeometricMean P.part (truncatedProfileWeight P (d n)) +
                Real.exp (-averagedProfileRate * Real.rpow (d n : ℝ) (2 / 3 : ℝ)) := by
  have hCpos : 0 < C := by linarith
  have hsmall := (degree_tendsto_atTop_of_log_lower hCpos hlog).eventually
    eventually_profile_prefactor_absorbed
  filter_upwards [eventually_valid_degrees hCpos hlog hsparse,
    eventually_weight_range_le_degree hC hlog hsparse, hsmall] with n hn hdiam hdegree
  intro hd r P hheight
  have hnpos : 0 < n := lt_trans hn.1 hn.2
  letI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  apply averaged_actual_profile P hd _ hdegree
  intro a b
  exact (truncatedProfileWeight_dyadic_range hnpos hn.1 P hheight a b).trans hdiam

end CircularLaw
