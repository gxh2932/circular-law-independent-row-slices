import CircularLaw.MatrixDiscrepancy

/-!
# Complete dyadic coordinate levels for the norm proof

The level of a coordinate is the least natural exponent whose power
of two bounds `sqrt(n)*abs(x_i)`. Level zero includes every coordinate
below `1/sqrt(n)`, as well as zero coordinates. The actual finite image
of these indices gives a complete partition without an assumed cover.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem exists_real_two_pow_ge (t : ℝ) : ∃ k : ℕ, t ≤ (2 : ℝ) ^ k := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt t (by norm_num : (1 : ℝ) < 2)
  exact ⟨k, hk.le⟩

def dyadicCeilIndex (t : ℝ) : ℕ := Nat.find (exists_real_two_pow_ge t)

theorem dyadicCeilIndex_upper (t : ℝ) : t ≤ (2 : ℝ) ^ dyadicCeilIndex t :=
  Nat.find_spec (exists_real_two_pow_ge t)

theorem dyadicCeilIndex_minimal (t : ℝ) {k : ℕ} (hk : k < dyadicCeilIndex t) :
    (2 : ℝ) ^ k < t := by
  exact lt_of_not_ge (Nat.find_min (exists_real_two_pow_ge t) hk)

theorem dyadicCeilIndex_eq_zero_iff (t : ℝ) : dyadicCeilIndex t = 0 ↔ t ≤ 1 := by
  constructor
  · intro h
    simpa only [h, pow_zero] using dyadicCeilIndex_upper t
  · intro h
    have hZero : dyadicCeilIndex t ≤ 0 := Nat.find_min' (exists_real_two_pow_ge t) (by simpa only [pow_zero] using h)
    omega

theorem dyadicCeilIndex_scale_le_twice {t : ℝ} (hIndex : 0 < dyadicCeilIndex t) :
    (2 : ℝ) ^ dyadicCeilIndex t ≤ 2 * t := by
  have hLow := dyadicCeilIndex_minimal t (show dyadicCeilIndex t - 1 < dyadicCeilIndex t by omega)
  have hPow : (2 : ℝ) ^ dyadicCeilIndex t = 2 * (2 : ℝ) ^ (dyadicCeilIndex t - 1) := by
    conv_lhs => rw [show dyadicCeilIndex t = dyadicCeilIndex t - 1 + 1 by omega]
    rw [pow_succ, mul_comm]
  rw [hPow]
  exact mul_le_mul_of_nonneg_left hLow.le (by norm_num)

def normCoordinateLevel {ι : Type*} (n : ℕ) (x : ι → ℝ) (i : ι) : ℕ :=
  dyadicCeilIndex (Real.sqrt n * |x i|)

def normCoordinateLevels {ι : Type*} [Fintype ι] (n : ℕ) (x : ι → ℝ) : Finset ℕ :=
  Finset.univ.image (normCoordinateLevel n x)

def normCoordinatePart {ι : Type*} [Fintype ι] (n : ℕ) (x : ι → ℝ) (k : ℕ) : Finset ι :=
  Finset.univ.filter (fun i => normCoordinateLevel n x i = k)

def normCoordinateMass {ι : Type*} [Fintype ι] (n : ℕ) (x : ι → ℝ) (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ k) ^ 2 / n * (normCoordinatePart n x k).card

theorem mem_normCoordinatePart {ι : Type*} [Fintype ι] (n : ℕ) (x : ι → ℝ) (i : ι) (k : ℕ) :
    i ∈ normCoordinatePart n x k ↔ normCoordinateLevel n x i = k := by
  simp only [normCoordinatePart, Finset.mem_filter, Finset.mem_univ, true_and]

theorem normCoordinateLevel_mem {ι : Type*} [Fintype ι] (n : ℕ) (x : ι → ℝ) (i : ι) :
    normCoordinateLevel n x i ∈ normCoordinateLevels n x :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem normCoordinatePart_nonempty_iff {ι : Type*} [Fintype ι] (n : ℕ) (x : ι → ℝ) (k : ℕ) :
    (normCoordinatePart n x k).Nonempty ↔ k ∈ normCoordinateLevels n x := by
  simp only [Finset.Nonempty, mem_normCoordinatePart, normCoordinateLevels, Finset.mem_image,
    Finset.mem_univ, true_and]

theorem normCoordinatePart_disjoint {ι : Type*} [Fintype ι] (n : ℕ) (x : ι → ℝ)
    {k l : ℕ} (hkl : k ≠ l) : Disjoint (normCoordinatePart n x k) (normCoordinatePart n x l) := by
  apply Finset.disjoint_left.mpr
  intro i hik hil
  exact hkl ((mem_normCoordinatePart n x i k).mp hik |>.symm.trans ((mem_normCoordinatePart n x i l).mp hil))

theorem normCoordinatePart_upper {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n)
    (x : ι → ℝ) {k : ℕ} {i : ι} (hi : i ∈ normCoordinatePart n x k) :
    |x i| ≤ (2 : ℝ) ^ k / Real.sqrt n := by
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h := dyadicCeilIndex_upper (Real.sqrt n * |x i|)
  change Real.sqrt n * |x i| ≤ (2 : ℝ) ^ normCoordinateLevel n x i at h
  rw [(mem_normCoordinatePart n x i k).mp hi] at h
  exact (le_div_iff₀ hRoot).mpr (by simpa only [mul_comm] using h)

theorem normCoordinatePart_positive_scale_bound {ι : Type*} [Fintype ι] {n : ℕ}
    (x : ι → ℝ) {k : ℕ} (hk : 0 < k) {i : ι} (hi : i ∈ normCoordinatePart n x k) :
    (2 : ℝ) ^ k ≤ 2 * Real.sqrt n * |x i| := by
  have hIndex : 0 < dyadicCeilIndex (Real.sqrt n * |x i|) := by
    simpa only [← (mem_normCoordinatePart n x i k).mp hi, normCoordinateLevel] using hk
  have h := dyadicCeilIndex_scale_le_twice hIndex
  change (2 : ℝ) ^ normCoordinateLevel n x i ≤ 2 * (Real.sqrt n * |x i|) at h
  rw [(mem_normCoordinatePart n x i k).mp hi] at h
  simpa only [mul_assoc] using h

end CircularLaw
