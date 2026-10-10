import CircularLaw.ProfileSmallBinMass

/-!
# The large-part product branch for actual truncated weights

The cutoff and spread masses are sums of the actual profile part sizes.
The three source weight cases give the K1 logarithmic bound and hence
the product decay, with the finite-size correction kept explicit.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def profileSelectedMass {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (S : Finset ι) : ℝ :=
  ∑ q ∈ S, (profilePartSize P q : ℝ)

def profileCutoffParts {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (d : ℕ) (κ : ℝ) : Finset ι :=
  Finset.univ.filter (fun q => Real.rpow (d : ℝ) (-κ) * Fintype.card α ≤
    (profilePartSize P q : ℝ))

def profileSpreadParts {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) : Finset ι := Finset.univ.filter (fun q => P.spread q = true)

theorem profileSelectedMass_eq_coordinate_card {α ι : Type*} [Fintype α] [DecidableEq ι]
    (P : RowProfile α ι) (S : Finset ι) :
    profileSelectedMass P S = ((Finset.univ.filter (fun a => P.part a ∈ S)).card : ℝ) := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset α) S P.part
  simpa only [profileSelectedMass, profilePartSize, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.mem_univ, true_and, Nat.cast_sum] using
      congrArg (fun t : ℕ => (t : ℝ)) h

theorem profileSelectedMass_total {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) : profileSelectedMass P Finset.univ = Fintype.card α := by
  rw [profileSelectedMass_eq_coordinate_card]
  simp

theorem profileSelectedMass_add_compl {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : RowProfile α ι) (S : Finset ι) :
    profileSelectedMass P S + profileSelectedMass P Sᶜ = Fintype.card α := by
  calc
    _ = profileSelectedMass P Finset.univ :=
      Finset.sum_add_sum_compl S (fun q => (profilePartSize P q : ℝ))
    _ = _ := profileSelectedMass_total P

theorem profileSelectedMass_mono {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) {S T : Finset ι} (h : S ⊆ T) :
    profileSelectedMass P S ≤ profileSelectedMass P T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.cast_nonneg _)

theorem profileCutoff_mass_dichotomy {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : RowProfile α ι) (d : ℕ) (κ R : ℝ) :
    (Fintype.card α : ℝ) - R / 4 ≤ profileSelectedMass P (profileCutoffParts P d κ) ∨
      R / 4 ≤ profileSelectedMass P (profileCutoffParts P d κ)ᶜ := by
  have hTotal := profileSelectedMass_add_compl P (profileCutoffParts P d κ)
  by_cases h : (Fintype.card α : ℝ) - R / 4 ≤ profileSelectedMass P (profileCutoffParts P d κ)
  · exact Or.inl h
  · exact Or.inr (by linarith)

theorem profileSpreadMass_le_large_add_small {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (P : RowProfile α ι) (S : Finset ι) :
    profileSelectedMass P (profileSpreadParts P) ≤
      profileSelectedMass P (S ∩ profileSpreadParts P) + profileSelectedMass P Sᶜ := by
  have hSplit : profileSelectedMass P (profileSpreadParts P) =
      profileSelectedMass P (S ∩ profileSpreadParts P) +
        profileSelectedMass P (Sᶜ ∩ profileSpreadParts P) := by
    unfold profileSelectedMass
    rw [← Finset.sum_union (Finset.disjoint_left.mpr (by
      intro q hq hr
      exact (Finset.mem_compl.mp (Finset.mem_inter.mp hr).1) (Finset.mem_inter.mp hq).1))]
    congr 1
    ext q
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
    tauto
  rw [hSplit]
  exact add_le_add_right (profileSelectedMass_mono P Finset.inter_subset_left) _

theorem profileCutoff_mass_lower {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (P : RowProfile α ι) {d : ℕ} {κ : ℝ} {q : ι}
    (hq : q ∈ profileCutoffParts P d κ) :
    Real.rpow (d : ℝ) (-κ) ≤ partMass P.part q := by
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [partMass_eq_profile_size]
  exact (le_div_iff₀ hn).mpr (Finset.mem_filter.mp hq).2

theorem profileCutoff_is_large {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (P : RowProfile α ι) {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : κ ≤ 1 / 3)
    {q : ι} (hq : q ∈ profileCutoffParts P d κ) : profileLargePart P d q := by
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact (Real.rpow_le_rpow_of_exponent_le hdOne (by linarith : (-1 / 3 : ℝ) ≤ -κ)).trans
    (profileCutoff_mass_lower P hq)

theorem profile_height_weight_log {α ι : Type*} [Fintype α] [Nonempty α]
    (P : RowProfile α ι) {d : ℕ} (hd : 0 < d) (q : ι) :
    Real.log ((P.height q : ℝ) / truncatedProfileWeight P d q) =
      if profileLargePart P d q then
        if P.spread q then -(Real.log d + Real.log (partMass P.part q)) / 2
        else -Real.log (partMass P.part q)
      else if P.spread q then 0 else Real.log d := by
  have hh : (0 : ℝ) < P.height q := by exact_mod_cast P.height_pos q
  have hm := rowProfile_mass_pos P q
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.log_div hh.ne' (truncatedProfileWeight_pos P hd q).ne']
  unfold truncatedProfileWeight profileLargePart
  split_ifs
  · rw [Real.log_mul hh.ne' (Real.sqrt_pos.mpr (mul_pos hdR hm)).ne',
      Real.log_sqrt (mul_pos hdR hm).le, Real.log_mul hdR.ne' hm.ne']
    ring
  · rw [Real.log_mul hh.ne' hm.ne']
    ring
  · ring
  · rw [Real.log_div hh.ne' hdR.ne']
    ring

theorem profile_height_weight_log_le_degree {α ι : Type*} [Fintype α] [Nonempty α]
    (P : RowProfile α ι) {d : ℕ} (hd : 0 < d) (q : ι) :
    Real.log ((P.height q : ℝ) / truncatedProfileWeight P d q) ≤ Real.log d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hLog : 0 ≤ Real.log d := Real.log_nonneg hdOne
  rw [profile_height_weight_log P hd q]
  by_cases hLarge : profileLargePart P d q
  · have hMassLog := Real.log_le_log (Real.rpow_pos_of_pos hdR (-1 / 3 : ℝ)) hLarge
    rw [Real.log_rpow hdR] at hMassLog
    simp only [hLarge, ↓reduceIte]
    split_ifs <;> linarith
  · simp only [hLarge, ↓reduceIte]
    split_ifs <;> linarith

theorem profileCutoff_height_weight_log {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι]
    (P : RowProfile α ι) {d : ℕ} (hd : 0 < d) {κ : ℝ}
    (hκ : 0 ≤ κ) (hκUpper : κ ≤ 1 / 3) (q : ι) :
    Real.log ((P.height q : ℝ) / truncatedProfileWeight P d q) ≤
      (κ - (if q ∈ profileCutoffParts P d κ ∩ profileSpreadParts P then 1 / 2 else 0) +
        (if q ∈ (profileCutoffParts P d κ)ᶜ then 1 else 0)) * Real.log d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have hκLog : 0 ≤ κ * Real.log d := mul_nonneg hκ hLog
  by_cases hq : q ∈ profileCutoffParts P d κ
  · have hLarge := profileCutoff_is_large P hd hκUpper hq
    have hMassLog := Real.log_le_log (Real.rpow_pos_of_pos hdR (-κ)) (profileCutoff_mass_lower P hq)
    rw [Real.log_rpow hdR] at hMassLog
    rw [profile_height_weight_log P hd q]
    simp only [hLarge, ↓reduceIte, Finset.mem_inter, hq, true_and,
      profileSpreadParts, Finset.mem_filter, Finset.mem_univ, Finset.mem_compl, not_true_eq_false]
    cases P.spread q <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  · have hBound := profile_height_weight_log_le_degree P hd q
    simp only [Finset.mem_inter, hq, false_and, ↓reduceIte, Finset.mem_compl,
      not_false_eq_true, sub_zero]
    nlinarith

theorem profile_height_weight_product_eq_exp {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) {d : ℕ} (hd : 0 < d) :
    (∏ q, ((P.height q : ℝ) / truncatedProfileWeight P d q) ^ profilePartSize P q) =
      Real.exp (∑ q, (profilePartSize P q : ℝ) *
        Real.log ((P.height q : ℝ) / truncatedProfileWeight P d q)) := by
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro q _
  rw [Real.exp_nat_mul, Real.exp_log (div_pos
    (by exact_mod_cast P.height_pos q) (truncatedProfileWeight_pos P hd q))]

theorem profile_height_weight_product_factorization {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (d : ℕ) :
    (∏ q, (P.height q : ℝ) ^ profilePartSize P q) *
      (∏ q, (truncatedProfileWeight P d q ^ profilePartSize P q)⁻¹) =
        ∏ q, ((P.height q : ℝ) / truncatedProfileWeight P d q) ^ profilePartSize P q := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q _
  rw [div_pow, div_eq_mul_inv]

theorem profile_K1_product_bound {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι]
    (P : RowProfile α ι) {d : ℕ} (hd : 0 < d) {κ R : ℝ}
    (hκ : 0 ≤ κ) (hκUpper : κ ≤ 1 / 3)
    (hSpread : R ≤ profileSelectedMass P (profileSpreadParts P))
    (hSmall : profileSelectedMass P (profileCutoffParts P d κ)ᶜ ≤ R / 4) :
    (∏ q, ((P.height q : ℝ) / truncatedProfileWeight P d q) ^ profilePartSize P q) ≤
      Real.rpow (d : ℝ) (κ * Fintype.card α - R / 8) := by
  let I := profileCutoffParts P d κ
  have hSplit := profileSpreadMass_le_large_add_small P I
  have hLarge : 3 * R / 4 ≤ profileSelectedMass P (I ∩ profileSpreadParts P) := by linarith
  have hLog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have hSum := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left (profileCutoff_height_weight_log P hd hκ hκUpper q)
      (Nat.cast_nonneg (profilePartSize P q) : (0 : ℝ) ≤ _))
  have hCollect : (∑ q, (profilePartSize P q : ℝ) *
      ((κ - (if q ∈ I ∩ profileSpreadParts P then 1 / 2 else 0) +
        (if q ∈ Iᶜ then 1 else 0)) * Real.log d)) =
      (κ * Fintype.card α - profileSelectedMass P (I ∩ profileSpreadParts P) / 2 +
        profileSelectedMass P Iᶜ) * Real.log d := by
    have hPoint (q : ι) : (profilePartSize P q : ℝ) *
        ((κ - (if q ∈ I ∩ profileSpreadParts P then 1 / 2 else 0) +
          (if q ∈ Iᶜ then 1 else 0)) * Real.log d) =
        ((profilePartSize P q : ℝ) * κ -
          (if q ∈ I ∩ profileSpreadParts P then (profilePartSize P q : ℝ) / 2 else 0) +
          (if q ∈ Iᶜ then (profilePartSize P q : ℝ) else 0)) * Real.log d := by
      split_ifs <;> ring
    simp_rw [hPoint]
    rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.sum_filter, ← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [← Finset.sum_div]
    change (profileSelectedMass P Finset.univ * κ -
      profileSelectedMass P (I ∩ profileSpreadParts P) / 2 +
      profileSelectedMass P Iᶜ) * Real.log d = _
    rw [profileSelectedMass_total]
    ring
  change _ ≤ ∑ q, (profilePartSize P q : ℝ) *
    ((κ - (if q ∈ I ∩ profileSpreadParts P then 1 / 2 else 0) +
      (if q ∈ Iᶜ then 1 else 0)) * Real.log d) at hSum
  rw [hCollect] at hSum
  have hExponent : κ * Fintype.card α - profileSelectedMass P (I ∩ profileSpreadParts P) / 2 +
      profileSelectedMass P Iᶜ ≤ κ * Fintype.card α - R / 8 := by linarith
  have hPower : Real.rpow (d : ℝ) (κ * Fintype.card α - R / 8) =
      Real.exp (Real.log d * (κ * Fintype.card α - R / 8)) :=
    Real.rpow_def_of_pos (by exact_mod_cast hd) _
  rw [profile_height_weight_product_eq_exp P hd, hPower]
  apply Real.exp_le_exp.mpr
  exact hSum.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hExponent hLog)

end CircularLaw
