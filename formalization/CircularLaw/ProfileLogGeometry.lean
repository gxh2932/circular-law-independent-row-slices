import CircularLaw.ProfileFactorialEntropy

/-!
# Logarithmic geometry of canonical profile weights

Size-height bounds and equality of dyadic weight bins yield geometric
decay along the creation orders inside each of the four source families.
The weight coefficients are exactly those of the truncated profile weight.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem profilePartSize_pos {α ι : Type*} [Fintype α] (P : RowProfile α ι) (q : ι) :
    0 < profilePartSize P q := by
  obtain ⟨a, ha⟩ := P.part_surjective q
  letI : Nonempty {a : α // P.part a = q} := ⟨⟨a, ha⟩⟩
  exact Nat.card_pos

theorem partMass_eq_profile_size {α ι : Type*} [Fintype α] (P : RowProfile α ι) (q : ι) :
    partMass P.part q = (profilePartSize P q : ℝ) / Fintype.card α := by
  simp only [partMass, uniformProbability, profilePartSize, Nat.card_eq_fintype_card]

def profileLargePart {α ι : Type*} [Fintype α] (P : RowProfile α ι) (d : ℕ) (q : ι) : Prop :=
  Real.rpow (d : ℝ) (-1 / 3 : ℝ) ≤ partMass P.part q

def profileBinFamily {α ι : Type*} [Fintype α] (P : RowProfile α ι) (d : ℕ) (q : ι) : Bool × Bool :=
  (P.spread q, decide (profileLargePart P d q))

def profileWeightLogCoefficient {α ι : Type*} [Fintype α] (P : RowProfile α ι)
    (d : ℕ) (q : ι) : ℝ := if profileLargePart P d q then if P.spread q then 1 / 2 else 1 else 0

def profileWeightLogOffset {α ι : Type*} [Fintype α] (P : RowProfile α ι)
    (d : ℕ) (q : ι) : ℝ :=
  if profileLargePart P d q then
    if P.spread q then (Real.log d - Real.log (Fintype.card α)) / 2
    else -Real.log (Fintype.card α)
  else if P.spread q then 0 else -Real.log d

theorem profileWeightLogCoefficient_bounds {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (d : ℕ) (q : ι) :
    0 ≤ profileWeightLogCoefficient P d q ∧ profileWeightLogCoefficient P d q ≤ 1 := by
  unfold profileWeightLogCoefficient
  split_ifs <;> norm_num

theorem profileBinFamily_log_data_eq {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (d : ℕ) {q r : ι} (h : profileBinFamily P d q = profileBinFamily P d r) :
    profileWeightLogCoefficient P d q = profileWeightLogCoefficient P d r ∧
      profileWeightLogOffset P d q = profileWeightLogOffset P d r := by
  have hSpread : P.spread q = P.spread r := congrArg Prod.fst h
  have hLarge : profileLargePart P d q ↔ profileLargePart P d r :=
    decide_eq_decide.mp (congrArg Prod.snd h)
  simp only [profileWeightLogCoefficient, profileWeightLogOffset, hSpread, hLarge]
  exact ⟨True.intro, True.intro⟩

theorem truncatedProfileWeight_log {α ι : Type*} [Fintype α] [Nonempty α]
    (P : RowProfile α ι) {d : ℕ} (hd : 0 < d) (q : ι) :
    Real.log (truncatedProfileWeight P d q) = Real.log (P.height q) +
      profileWeightLogCoefficient P d q * Real.log (profilePartSize P q) +
        profileWeightLogOffset P d q := by
  have hh : (0 : ℝ) < P.height q := by exact_mod_cast P.height_pos q
  have hs : (0 : ℝ) < profilePartSize P q := by exact_mod_cast profilePartSize_pos P q
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hm : 0 < partMass P.part q := rowProfile_mass_pos P q
  have hmLog : Real.log (partMass P.part q) =
      Real.log (profilePartSize P q) - Real.log (Fintype.card α) := by
    rw [partMass_eq_profile_size, Real.log_div hs.ne' hn.ne']
  unfold truncatedProfileWeight profileWeightLogCoefficient profileWeightLogOffset profileLargePart
  split_ifs
  · rw [Real.log_mul hh.ne' (Real.sqrt_pos.mpr (mul_pos hdR hm)).ne',
      Real.log_sqrt (mul_pos hdR hm).le, Real.log_mul hdR.ne' hm.ne', hmLog]
    ring
  · rw [Real.log_mul hh.ne' hm.ne', hmLog]
    ring
  · ring
  · rw [Real.log_div hh.ne' hdR.ne']
    ring

structure ProfileOrderGeometry {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (order : ι → ℕ) : Prop where
  injective : Function.Injective (fun q => (P.spread q, order q))
  lower : ∀ q, (2 : ℝ) ^ ((order q : ℤ) - 1) * (P.height q : ℝ) ≤ (profilePartSize P q : ℝ)
  upper : ∀ q, (profilePartSize P q : ℝ) ≤ (2 : ℝ) ^ ((order q : ℤ) + 1) * (P.height q : ℝ)

theorem profile_order_log_size_height {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order) (q : ι) :
    Real.log (P.height q) + ((order q : ℝ) - 1) * Real.log 2 ≤ Real.log (profilePartSize P q) ∧
      Real.log (profilePartSize P q) ≤ Real.log (P.height q) + ((order q : ℝ) + 1) * Real.log 2 := by
  have hh : (0 : ℝ) < P.height q := by exact_mod_cast P.height_pos q
  have hs : (0 : ℝ) < profilePartSize P q := by exact_mod_cast profilePartSize_pos P q
  have hLow := Real.log_le_log (mul_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _) hh) (hGeometry.lower q)
  have hHigh := Real.log_le_log hs (hGeometry.upper q)
  rw [Real.log_mul (by positivity) hh.ne', Real.log_zpow] at hLow hHigh
  simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one] at hLow hHigh
  exact ⟨by linarith, by linarith⟩

theorem equal_dyadic_order_log_gap {w v : ℝ}
    (h : Int.floor (Real.logb 2 w) = Int.floor (Real.logb 2 v)) :
    Real.log w - Real.log v ≤ Real.log 2 := by
  have hTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLow := Int.floor_le (Real.logb 2 v)
  have hHigh := Int.lt_floor_add_one (Real.logb 2 w)
  rw [h] at hHigh
  simp only [Real.logb] at hLow hHigh
  have hLowScaled := (le_div_iff₀ hTwo).mp hLow
  have hHighScaled := (div_lt_iff₀ hTwo).mp hHigh
  linarith

theorem linear_log_size_pair_bound {a b u v β j l L : ℝ}
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (hβOne : β ≤ 1) (hjl : j ≤ l)
    (hA : a ≤ u + (j + 1) * L) (hB : v + (l - 1) * L ≤ b)
    (hWeight : u - v + β * (a - b) ≤ L) :
    a - b ≤ 3 * L + (j - l) * L / 2 := by
  have hMain : (1 + β) * (a - b) ≤ (3 + j - l) * L := by
    nlinarith only [hA, hB, hWeight]
  have hβL := mul_nonneg hβ hL
  have hDiff : 0 ≤ (β - 1) * ((j - l) * L) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (mul_nonpos_of_nonpos_of_nonneg (by linarith) hL)
  have hCompare : (3 + j - l) * L ≤ (1 + β) * (3 * L + (j - l) * L / 2) := by
    nlinarith only [hβL, hDiff]
  exact le_of_mul_le_mul_left (hMain.trans hCompare) (by linarith)

theorem profile_same_family_log_size_pair {α ι : Type*} [Fintype α] [Nonempty α]
    (P : RowProfile α ι) (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order)
    {d : ℕ} (hd : 0 < d) {q r : ι}
    (hFamily : profileBinFamily P d q = profileBinFamily P d r)
    (hBin : dyadicProfilePartOrder P d q = dyadicProfilePartOrder P d r)
    (hOrder : order q ≤ order r) :
    Real.log (profilePartSize P q) - Real.log (profilePartSize P r) ≤
      3 * Real.log 2 - ((order r : ℝ) - (order q : ℝ)) / 4 := by
  have hLogQ := truncatedProfileWeight_log P hd q
  have hLogR := truncatedProfileWeight_log P hd r
  obtain ⟨hCoeff, hOffset⟩ := profileBinFamily_log_data_eq P d hFamily
  have hGap := equal_dyadic_order_log_gap hBin
  rw [hLogQ, hLogR, ← hCoeff, ← hOffset] at hGap
  have hWeight : Real.log (P.height q) - Real.log (P.height r) +
      profileWeightLogCoefficient P d q *
        (Real.log (profilePartSize P q) - Real.log (profilePartSize P r)) ≤ Real.log 2 := by
    nlinarith only [hGap]
  have hBounds := profileWeightLogCoefficient_bounds P d q
  have hOrderR : (order q : ℝ) ≤ order r := by exact_mod_cast hOrder
  have hTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
    norm_num at h
    linarith
  have h := linear_log_size_pair_bound (by linarith : 0 ≤ Real.log 2) hBounds.1 hBounds.2 hOrderR
    (profile_order_log_size_height P order hGeometry q).2
    (profile_order_log_size_height P order hGeometry r).1 hWeight
  have hCompare := mul_le_mul_of_nonneg_right hTwo (sub_nonneg.mpr hOrderR)
  nlinarith only [h, hCompare]

theorem profile_same_family_size_decay {α ι : Type*} [Fintype α] [Nonempty α]
    (P : RowProfile α ι) (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order)
    {d : ℕ} (hd : 0 < d) {q r : ι}
    (hFamily : profileBinFamily P d q = profileBinFamily P d r)
    (hBin : dyadicProfilePartOrder P d q = dyadicProfilePartOrder P d r)
    (hOrder : order q ≤ order r) :
    (profilePartSize P q : ℝ) ≤ 8 * (profilePartSize P r : ℝ) *
      Real.exp (-((order r : ℝ) - (order q : ℝ)) / 4) := by
  have hsQ : (0 : ℝ) < profilePartSize P q := by exact_mod_cast profilePartSize_pos P q
  have hsR : (0 : ℝ) < profilePartSize P r := by exact_mod_cast profilePartSize_pos P r
  have hLog := profile_same_family_log_size_pair P order hGeometry hd hFamily hBin hOrder
  have hEight : Real.exp (3 * Real.log 2) = 8 := by
    rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  calc
    (profilePartSize P q : ℝ) = Real.exp (Real.log (profilePartSize P q)) := (Real.exp_log hsQ).symm
    _ ≤ Real.exp (Real.log (profilePartSize P r) + 3 * Real.log 2 +
        (-((order r : ℝ) - (order q : ℝ)) / 4)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hsR, hEight]
      ring

end CircularLaw
