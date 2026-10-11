import CircularLaw.Binomial
import CircularLaw.MaxWeight

/-!
# Averaging the row-profile estimator

The coordinate map `part` specifies the partition, and its masses are taken
under the genuine uniform coordinate law. The estimator is the minimum over
visited parts in equations (SB-actual) and (SB-truncated). The sample-index
formula below is proved equal to that minimum, including repeated samples.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def partMass {α ι : Type*} [Fintype α] (part : α → ι) (q : ι) : ℝ :=
  uniformProbability (fun a => part a = q)

def visitedParts {α ι : Type*} (part : α → ι) {d : ℕ} (samples : Fin d → α) :
    Finset ι := by
  classical
  exact Finset.univ.image (fun i => part (samples i))

theorem mem_visitedParts_iff {α ι : Type*} (part : α → ι) {d : ℕ}
    (samples : Fin d → α) (q : ι) :
    q ∈ visitedParts part samples ↔ 0 < trialCount (fun a => part a = q) samples := by
  classical
  simp only [visitedParts, Finset.mem_image, Finset.mem_univ, true_and,
    trialCount, Finset.card_pos, Finset.filter_nonempty_iff, Finset.mem_univ, true_and]

theorem visitedParts_nonempty {α ι : Type*} (part : α → ι) {d : ℕ} (hd : 0 < d)
    (samples : Fin d → α) : (visitedParts part samples).Nonempty := by
  classical
  exact Finset.Nonempty.image ⟨⟨0, hd⟩, Finset.mem_univ _⟩ _

def profileEstimator {α ι : Type*} (part : α → ι) (w : ι → ℝ) {d : ℕ}
    (hd : 0 < d) (samples : Fin d → α) : ℝ :=
  min 1 (Finset.univ.inf' ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    (fun i => (w (part (samples i)))⁻¹))

/-- This is precisely the minimum over `q` with `Q_q > 0`, rather than a
different statistic on ordered samples. -/
theorem profileEstimator_eq_visited_min {α ι : Type*} (part : α → ι) (w : ι → ℝ)
    {d : ℕ} (hd : 0 < d) (samples : Fin d → α) :
    profileEstimator part w hd samples =
      min 1 ((visitedParts part samples).inf' (visitedParts_nonempty part hd samples)
        (fun q => (w q)⁻¹)) := by
  classical
  unfold profileEstimator visitedParts
  rw [Finset.inf'_image]
  rfl

theorem profileEstimator_le_one {α ι : Type*} (part : α → ι) (w : ι → ℝ)
    {d : ℕ} (hd : 0 < d) (samples : Fin d → α) :
    profileEstimator part w hd samples ≤ 1 := min_le_left _ _

theorem profileEstimator_nonneg {α ι : Type*} (part : α → ι) (w : ι → ℝ)
    {d : ℕ} (hd : 0 < d) (samples : Fin d → α)
    (hw : ∀ i, 0 ≤ w (part (samples i))) :
    0 ≤ profileEstimator part w hd samples := by
  apply le_min (by norm_num)
  exact Finset.le_inf' _ _ (fun i _ => inv_nonneg.mpr (hw i))

theorem profileEstimator_le_sample_inv {α ι : Type*} (part : α → ι) (w : ι → ℝ)
    {d : ℕ} (hd : 0 < d) (samples : Fin d → α) (i : Fin d) :
    profileEstimator part w hd samples ≤ (w (part (samples i)))⁻¹ :=
  (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ i))

/-- Multiplying every visited weight by at least one half increases the
truncated estimator by at most a factor of two. -/
theorem profileEstimator_compare {α ι : Type*} (part : α → ι) (w v : ι → ℝ)
    {d : ℕ} (hd : 0 < d) (samples : Fin d → α)
    (hv : ∀ i, 0 < v (part (samples i)))
    (hwv : ∀ i, v (part (samples i)) / 2 ≤ w (part (samples i))) :
    profileEstimator part w hd samples ≤ 2 * profileEstimator part v hd samples := by
  classical
  change _ ≤ 2 * min 1 (Finset.univ.inf' _ (fun i => (v (part (samples i)))⁻¹))
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  apply le_min
  · have h := profileEstimator_le_one part w hd samples
    linarith
  · rcases Finset.exists_mem_eq_inf'
      (⟨⟨0, hd⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin d)).Nonempty)
      (fun i => (v (part (samples i)))⁻¹) with ⟨i, _, hi⟩
    have hwi : 0 < w (part (samples i)) := lt_of_lt_of_le (half_pos (hv i)) (hwv i)
    have hinv := (inv_le_inv₀ hwi (half_pos (hv i))).mpr (hwv i)
    have hb := profileEstimator_le_sample_inv part w hd samples i
    change profileEstimator part w hd samples ≤
      2 * (Finset.univ.inf' _ (fun i => (v (part (samples i)))⁻¹))
    rw [hi]
    have he : (v (part (samples i)) / 2)⁻¹ = 2 * (v (part (samples i)))⁻¹ := by
      rw [inv_div, div_eq_mul_inv]
    rw [he] at hinv
    exact hb.trans hinv

def dyadicWeight (w : ℝ) : ℝ := (Int.floor (Real.logb 2 w) : ℝ)

theorem inverse_le_dyadic_exp {w : ℝ} (hw : 0 < w) :
    w⁻¹ ≤ Real.exp (-Real.log 2 * dyadicWeight w) := by
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hfloor : dyadicWeight w ≤ Real.log w / Real.log 2 := Int.floor_le _
  have hmul : Real.log 2 * dyadicWeight w ≤ Real.log w := by
    simpa only [mul_comm] using (le_div_iff₀ hlog).mp hfloor
  calc
    _ = Real.exp (-Real.log w) := by rw [Real.exp_neg, Real.exp_log hw]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem profileEstimator_le_dyadic_max {α ι : Type*} (part : α → ι) (w : ι → ℝ)
    {d : ℕ} (hd : 0 < d) (samples : Fin d → α)
    (hw : ∀ a, 0 < w (part a)) :
    profileEstimator part w hd samples ≤ Real.exp (-Real.log 2 *
      sampleMaximum (fun a => dyadicWeight (w (part a))) hd samples) := by
  classical
  rcases Finset.exists_mem_eq_sup'
    (⟨⟨0, hd⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin d)).Nonempty)
    (fun i => dyadicWeight (w (part (samples i)))) with ⟨i, _, hi⟩
  change _ ≤ Real.exp (-Real.log 2 * Finset.univ.sup' _ _)
  rw [hi]
  exact (profileEstimator_le_sample_inv part w hd samples i).trans
    (inverse_le_dyadic_exp (hw (samples i)))

def profileGeometricMean {α ι : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (w : ι → ℝ) : ℝ :=
  ∏ q, Real.rpow (w q) (-partMass part q)

theorem finiteMean_part_function {α ι : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (f : ι → ℝ) :
    finiteMean (fun a => f (part a)) = ∑ q, partMass part q * f q := by
  classical
  have hpoint (a : α) : f (part a) =
      ∑ q, (if part a = q then (1 : ℝ) else 0) * f q := by simp
  simp_rw [hpoint]
  rw [finiteMean_finset_sum]
  simp only [finiteMean_mul_const, finiteMean_indicator, partMass]

theorem profileGeometricMean_eq_exp {α ι : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (w : ι → ℝ) (hw : ∀ q, 0 < w q) :
    profileGeometricMean part w = Real.exp (-finiteMean (fun a => Real.log (w (part a)))) := by
  unfold profileGeometricMean
  simp only [Real.rpow_eq_pow, Real.rpow_def_of_pos (hw _)]
  rw [← Real.exp_sum, finiteMean_part_function part (fun q => Real.log (w q))]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem dyadic_mean_geometric_bound {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (part : α → ι) (w : ι → ℝ) (hw : ∀ q, 0 < w q) :
    Real.exp (-Real.log 2 * finiteMean (fun a => dyadicWeight (w (part a)))) ≤
      2 * profileGeometricMean part w := by
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hpoint (a : α) : Real.log (w (part a)) / Real.log 2 - 1 ≤
      dyadicWeight (w (part a)) := (Int.sub_one_lt_floor _).le
  have hm := finiteMean_mono hpoint
  have hmean : finiteMean (fun a => Real.log (w (part a)) / Real.log 2 - 1) =
      finiteMean (fun a => Real.log (w (part a))) / Real.log 2 - 1 := by
    simp only [div_eq_mul_inv, finiteMean_sub, finiteMean_mul_const, finiteMean_const]
  rw [hmean] at hm
  have hb : -Real.log 2 * finiteMean (fun a => dyadicWeight (w (part a))) ≤
      Real.log 2 - finiteMean (fun a => Real.log (w (part a))) := by
    have h := (mul_le_mul_of_nonneg_left hm hlog.le)
    field_simp at h
    linarith
  calc
    _ ≤ Real.exp (Real.log 2 - finiteMean (fun a => Real.log (w (part a)))) :=
      Real.exp_le_exp.mpr hb
    _ = _ := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        profileGeometricMean_eq_exp part w hw, Real.exp_neg]
      rfl

/-- The dyadic geometric-mean and dispersion estimate for the precise
truncated estimator in the paper, with constants `epsilon = 1/12` and
`c = log 2 / 4`. -/
theorem averaged_truncated_profile {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (part : α → ι) (w : ι → ℝ) (hw : ∀ q, 0 < w q) {d : ℕ} (hd : 2 ≤ d)
    (hrange : ∀ a b, |dyadicWeight (w (part a)) - dyadicWeight (w (part b))| ≤ (d : ℝ) / 12) :
    finiteMean (fun samples : Fin d → α => profileEstimator part w (by omega) samples) ≤
      2 * Real.exp (-(Real.log 2 / 4) * pairDispersion (fun a => dyadicWeight (w (part a)))) *
        profileGeometricMean part w := by
  calc
    _ ≤ finiteMean (fun samples : Fin d → α => Real.exp (-Real.log 2 *
        sampleMaximum (fun a => dyadicWeight (w (part a))) (by omega) samples)) :=
      finiteMean_mono (fun samples => profileEstimator_le_dyadic_max part w (by omega) samples
        (fun a => hw (part a)))
    _ ≤ Real.exp (-Real.log 2 * finiteMean (fun a => dyadicWeight (w (part a))) -
        (Real.log 2 / 4) * pairDispersion (fun a => dyadicWeight (w (part a)))) :=
      max_weight_finite _ hd hrange
    _ = Real.exp (-Real.log 2 * finiteMean (fun a => dyadicWeight (w (part a)))) *
        Real.exp (-(Real.log 2 / 4) * pairDispersion (fun a => dyadicWeight (w (part a)))) := by
      rw [← Real.exp_add]
      congr 1; ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (dyadic_mean_geometric_bound part w hw)
        (Real.exp_nonneg (-(Real.log 2 / 4) * pairDispersion (fun a => dyadicWeight (w (part a)))))
      convert h using 1; ring

/-- The data used by the estimator: a nonempty-part partition, integer
heights, and the regular/spread distinction. The geometric hypotheses of
the canonical decomposition enter the separate planar small-ball theorem. -/
structure RowProfile (α ι : Type*) where
  part : α → ι
  part_surjective : Function.Surjective part
  height : ι → ℕ
  height_pos : ∀ q, 0 < height q
  spread : ι → Bool

def actualProfileWeight {α ι : Type*} (P : RowProfile α ι) {d : ℕ}
    (samples : Fin d → α) (q : ι) : ℝ :=
  if P.spread q then (P.height q : ℝ) * Real.sqrt (trialCount (fun a => P.part a = q) samples)
  else (P.height q : ℝ) * trialCount (fun a => P.part a = q) samples / d

def truncatedProfileWeight {α ι : Type*} [Fintype α] (P : RowProfile α ι)
    (d : ℕ) (q : ι) : ℝ := by
  classical
  exact if Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤ partMass P.part q then
    if P.spread q then (P.height q : ℝ) * Real.sqrt ((d : ℝ) * partMass P.part q)
    else (P.height q : ℝ) * partMass P.part q
  else if P.spread q then (P.height q : ℝ) else (P.height q : ℝ) / d

def profileGood {α ι : Type*} [Fintype α] (P : RowProfile α ι) {d : ℕ}
    (samples : Fin d → α) : Prop :=
  ∀ q, Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤ partMass P.part q →
    (d : ℝ) * partMass P.part q / 2 ≤ trialCount (fun a => P.part a = q) samples

theorem rowProfile_mass_pos {α ι : Type*} [Fintype α] (P : RowProfile α ι) (q : ι) :
    0 < partMass P.part q := by
  classical
  rcases P.part_surjective q with ⟨a, ha⟩
  letI : Nonempty {a // P.part a = q} := ⟨⟨a, ha⟩⟩
  exact uniformProbability_pos_of_card_pos _ Nat.card_pos

theorem truncatedProfileWeight_pos {α ι : Type*} [Fintype α] (P : RowProfile α ι)
    {d : ℕ} (hd : 0 < d) (q : ι) : 0 < truncatedProfileWeight P d q := by
  classical
  have hh : (0 : ℝ) < P.height q := by exact_mod_cast P.height_pos q
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hp := rowProfile_mass_pos P q
  unfold truncatedProfileWeight
  split_ifs <;> positivity

theorem actualProfileWeight_nonneg {α ι : Type*} (P : RowProfile α ι) {d : ℕ}
    (samples : Fin d → α) (q : ι) : 0 ≤ actualProfileWeight P samples q := by
  unfold actualProfileWeight
  split_ifs <;> positivity

theorem trialCount_pos_of_sample {α ι : Type*} (part : α → ι) {d : ℕ}
    (samples : Fin d → α) (i : Fin d) :
    0 < trialCount (fun a => part a = part (samples i)) samples := by
  classical
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- On the paper's good occupancy event, every visited actual weight is
at least half the truncated weight. -/
theorem actualProfileWeight_ge_half {α ι : Type*} [Fintype α] (P : RowProfile α ι)
    {d : ℕ} (hd : 0 < d) (samples : Fin d → α) (hgood : profileGood P samples)
    (q : ι) (hvisited : 0 < trialCount (fun a => P.part a = q) samples) :
    truncatedProfileWeight P d q / 2 ≤ actualProfileWeight P samples q := by
  classical
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hh : (0 : ℝ) < P.height q := by exact_mod_cast P.height_pos q
  have hp := rowProfile_mass_pos P q
  have hcount : (1 : ℝ) ≤ trialCount (fun a => P.part a = q) samples := by exact_mod_cast hvisited
  unfold truncatedProfileWeight actualProfileWeight
  by_cases hlarge : Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤ partMass P.part q
  · rw [if_pos hlarge]
    have hg := hgood q hlarge
    by_cases hs : P.spread q = true
    · simp only [if_pos hs]
      have hsqrt : Real.sqrt ((d : ℝ) * partMass P.part q) / 2 ≤
          Real.sqrt (trialCount (fun a => P.part a = q) samples) := by
        apply (Real.le_sqrt (by positivity) (by positivity)).mpr
        rw [div_pow, Real.sq_sqrt (mul_nonneg hd'.le hp.le)]
        norm_num
        linarith
      have h := mul_le_mul_of_nonneg_left hsqrt hh.le
      simpa only [mul_div_assoc] using h
    · simp only [if_neg hs]
      apply (le_div_iff₀ hd').mpr
      have h := mul_le_mul_of_nonneg_left hg hh.le
      convert h using 1; ring
  · rw [if_neg hlarge]
    by_cases hs : P.spread q = true
    · simp only [if_pos hs]
      have hsqrt : (1 : ℝ) ≤ Real.sqrt (trialCount (fun a => P.part a = q) samples) := by
        exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hcount)
      nlinarith
    · simp only [if_neg hs]
      apply (le_div_iff₀ hd').mpr
      have hmul := mul_le_mul_of_nonneg_left hcount hh.le
      field_simp
      nlinarith

theorem profile_good_failure {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (P : RowProfile α ι) {d : ℕ} (hd : 0 < d) :
    uniformProbability (fun samples : Fin d → α => ¬ profileGood P samples) ≤
      Real.rpow (d : ℝ) (1 / 3 : ℝ) *
        Real.exp (-binomialHalfRate * Real.rpow (d : ℝ) (2 / 3 : ℝ)) := by
  classical
  have h := multinomial_large_parts_failure P.part
    (Finset.univ.filter (fun q => Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤ partMass P.part q)) hd
    (fun _ hq => (Finset.mem_filter.mp hq).2)
  simpa only [profileGood, not_forall, not_le, exists_prop, Finset.mem_filter,
    Finset.mem_univ, true_and, partMass] using h

theorem actual_truncated_profile_comparison {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (P : RowProfile α ι) {d : ℕ} (hd : 0 < d) :
    finiteMean (fun samples : Fin d → α =>
      profileEstimator P.part (actualProfileWeight P samples) hd samples) ≤
      2 * finiteMean (fun samples : Fin d → α =>
        profileEstimator P.part (truncatedProfileWeight P d) hd samples) +
          Real.rpow (d : ℝ) (1 / 3 : ℝ) *
            Real.exp (-binomialHalfRate * Real.rpow (d : ℝ) (2 / 3 : ℝ)) := by
  classical
  have hpoint (samples : Fin d → α) :
      profileEstimator P.part (actualProfileWeight P samples) hd samples ≤
        2 * profileEstimator P.part (truncatedProfileWeight P d) hd samples +
          (if ¬ profileGood P samples then (1 : ℝ) else 0) := by
    by_cases hg : profileGood P samples
    · rw [if_neg (not_not.mpr hg), add_zero]
      exact profileEstimator_compare P.part _ _ hd samples
        (fun i => truncatedProfileWeight_pos P hd (P.part (samples i)))
        (fun i => actualProfileWeight_ge_half P hd samples hg _
          (trialCount_pos_of_sample P.part samples i))
    · rw [if_pos hg]
      have hnonneg := profileEstimator_nonneg P.part (truncatedProfileWeight P d) hd samples
        (fun i => (truncatedProfileWeight_pos P hd (P.part (samples i))).le)
      linarith [profileEstimator_le_one P.part (actualProfileWeight P samples) hd samples]
  have h := finiteMean_mono hpoint
  rw [finiteMean_add, finiteMean_const_mul, finiteMean_indicator] at h
  exact h.trans (add_le_add le_rfl (profile_good_failure P hd))

/-- A bound valid at every degree `d >= 2`, retaining the occupancy-tail
prefactor until the large-degree condition has been proved. -/
theorem averaged_actual_profile_prefactor {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (P : RowProfile α ι) {d : ℕ} (hd : 2 ≤ d)
    (hrange : ∀ a b,
      |dyadicWeight (truncatedProfileWeight P d (P.part a)) -
        dyadicWeight (truncatedProfileWeight P d (P.part b))| ≤ (d : ℝ) / 12) :
    finiteMean (fun samples : Fin d → α =>
      profileEstimator P.part (actualProfileWeight P samples) (by omega) samples) ≤
      4 * Real.exp (-(Real.log 2 / 4) *
        pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) *
          profileGeometricMean P.part (truncatedProfileWeight P d) +
            Real.rpow (d : ℝ) (1 / 3 : ℝ) *
              Real.exp (-binomialHalfRate * Real.rpow (d : ℝ) (2 / 3 : ℝ)) := by
  have htrunc := averaged_truncated_profile P.part (truncatedProfileWeight P d)
    (truncatedProfileWeight_pos P (by omega)) hd hrange
  have h := actual_truncated_profile_comparison P (by omega : 0 < d)
  have hh := mul_le_mul_of_nonneg_left htrunc (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

def averagedProfileRate : ℝ := min (Real.log 2 / 4) (binomialHalfRate / 2)

theorem averagedProfileRate_pos : 0 < averagedProfileRate :=
  lt_min (div_pos (Real.log_pos (by norm_num)) (by norm_num))
    (half_pos binomialHalfRate_pos)

/-- The first inequality of the averaged-profile proposition. The explicit
large-degree condition is the absorption of the preceding Chernoff prefactor. -/
theorem averaged_actual_profile {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (P : RowProfile α ι) {d : ℕ} (hd : 2 ≤ d)
    (hrange : ∀ a b,
      |dyadicWeight (truncatedProfileWeight P d (P.part a)) -
        dyadicWeight (truncatedProfileWeight P d (P.part b))| ≤ (d : ℝ) / 12)
    (hdegree : Real.rpow (d : ℝ) (1 / 3 : ℝ) *
      Real.exp (-binomialHalfRate * Real.rpow (d : ℝ) (2 / 3 : ℝ)) ≤
        Real.exp (-(binomialHalfRate / 2) * Real.rpow (d : ℝ) (2 / 3 : ℝ))) :
    finiteMean (fun samples : Fin d → α =>
      profileEstimator P.part (actualProfileWeight P samples) (by omega) samples) ≤
      4 * Real.exp (-averagedProfileRate *
        pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) *
          profileGeometricMean P.part (truncatedProfileWeight P d) +
            Real.exp (-averagedProfileRate * Real.rpow (d : ℝ) (2 / 3 : ℝ)) := by
  apply (averaged_actual_profile_prefactor P hd hrange).trans
  apply add_le_add
  · have hD := pairDispersion_nonneg
      (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))
    have hexp : Real.exp (-(Real.log 2 / 4) *
        pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) ≤
          Real.exp (-averagedProfileRate *
            pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right (min_le_left (Real.log 2 / 4) (binomialHalfRate / 2)) hD
      dsimp [averagedProfileRate]
      linarith
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num))
    rw [profileGeometricMean_eq_exp _ _ (truncatedProfileWeight_pos P (by omega))]
    exact Real.exp_nonneg _
  · apply hdegree.trans
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right
      (min_le_right (Real.log 2 / 4) (binomialHalfRate / 2))
      (Real.rpow_nonneg (Nat.cast_nonneg d) (2 / 3 : ℝ))
    dsimp [averagedProfileRate]
    linarith

/-- A closed target for the estimator conclusion, with its absolute
large-degree threshold made explicit. This does not assert the separate
planar concentration conclusion of `prop:averaged-profile`. -/
def AveragedEstimatorLemma : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ,
    ∀ n r d : ℕ, 0 < n → ∀ hd : 2 ≤ d, d₀ ≤ d →
      ∀ P : RowProfile (Fin n) (Fin r),
        (∀ a b, |dyadicWeight (truncatedProfileWeight P d (P.part a)) -
          dyadicWeight (truncatedProfileWeight P d (P.part b))| ≤ ε * d) →
        finiteMean (fun samples : Fin d → Fin n =>
          profileEstimator P.part (actualProfileWeight P samples) (by omega) samples) ≤
          C * Real.exp (-c *
            pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) *
              profileGeometricMean P.part (truncatedProfileWeight P d) +
                Real.exp (-c * Real.rpow (d : ℝ) (2 / 3 : ℝ))

theorem averaged_estimator_lemma : AveragedEstimatorLemma := by
  rcases Filter.eventually_atTop.mp eventually_profile_prefactor_absorbed with ⟨d₀, h₀⟩
  refine ⟨1 / 12, by norm_num, averagedProfileRate, averagedProfileRate_pos,
    4, by norm_num, d₀, ?_⟩
  intro n r d hn hd hlarge P hrange
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply averaged_actual_profile P hd _ (h₀ d hlarge)
  intro a b
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hrange a b

end CircularLaw
