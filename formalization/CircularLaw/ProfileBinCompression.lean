import CircularLaw.ProfileLogGeometry
import CircularLaw.FourFamilyEntropy

/-!
# Local compression of the actual profile bins

Each family uses the distance from its largest creation order as an age.
The size-height geometry gives the exponential mass bound, and the family
and age together identify every part. Thus local factorial compression is
proved from the explicit creation-order geometry, rather than assumed.
-/

noncomputable section
open Classical
open scoped BigOperators Nat

namespace CircularLaw

def profileBinMaxOrder {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (order : ι → ℕ) (d : ℕ) (b : ℤ) (family : Bool × Bool) : ℕ :=
  ((dyadicProfileBinParts P d b).filter (fun q => profileBinFamily P d q = family)).sup order

def profileBinAge {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (order : ι → ℕ) (d : ℕ) (b : ℤ) (q : ι) : ℕ :=
  profileBinMaxOrder P order d b (profileBinFamily P d q) - order q

theorem profile_bin_order_le_max {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (order : ι → ℕ) (d : ℕ) (b : ℤ)
    {q : ι} (hq : q ∈ dyadicProfileBinParts P d b) :
    order q ≤ profileBinMaxOrder P order d b (profileBinFamily P d q) :=
  Finset.le_sup (Finset.mem_filter.mpr ⟨hq, rfl⟩)

theorem profile_bin_code_injective {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order)
    (d : ℕ) (b : ℤ) :
    Set.InjOn (fun q => (profileBinFamily P d q, (profileBinAge P order d b q : ℤ)))
      (dyadicProfileBinParts P d b : Set ι) := by
  intro q hq r hr hCode
  have hFamily : profileBinFamily P d q = profileBinFamily P d r :=
    congrArg Prod.fst hCode
  have hCastAge : (profileBinAge P order d b q : ℤ) =
      (profileBinAge P order d b r : ℤ) := congrArg Prod.snd hCode
  have hAge : profileBinAge P order d b q = profileBinAge P order d b r := by
    exact_mod_cast hCastAge
  have hQ := profile_bin_order_le_max P order d b hq
  have hR := profile_bin_order_le_max P order d b hr
  have hMax : profileBinMaxOrder P order d b (profileBinFamily P d q) =
      profileBinMaxOrder P order d b (profileBinFamily P d r) := congrArg _ hFamily
  have hOrder : order q = order r := by
    dsimp [profileBinAge] at hAge
    omega
  have hSpread : P.spread q = P.spread r := congrArg Prod.fst hFamily
  exact hGeometry.injective (Prod.ext hSpread hOrder)

theorem profile_bin_size_tail {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (P : RowProfile α ι) (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order)
    {d : ℕ} (hd : 0 < d) (b : ℤ) {q : ι} (hq : q ∈ dyadicProfileBinParts P d b) :
    (profilePartSize P q : ℝ) ≤ 8 * (dyadicProfileHistogram P d b : ℝ) *
      Real.exp (-(profileBinAge P order d b q : ℝ) / 4) := by
  have hNonempty : ((dyadicProfileBinParts P d b).filter
      (fun r => profileBinFamily P d r = profileBinFamily P d q)).Nonempty :=
    ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩⟩
  obtain ⟨r, hr, hSup⟩ := Finset.exists_mem_eq_sup _ hNonempty order
  change profileBinMaxOrder P order d b (profileBinFamily P d q) = order r at hSup
  have hrBin := (Finset.mem_filter.mp hr).1
  have hFamily := (Finset.mem_filter.mp hr).2
  have hOrder := (profile_bin_order_le_max P order d b hq).trans_eq hSup
  have hBin : dyadicProfilePartOrder P d q = dyadicProfilePartOrder P d r :=
    (Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hrBin).2.symm
  have hDecay := profile_same_family_size_decay P order hGeometry hd hFamily.symm hBin hOrder
  have hAge : (profileBinAge P order d b q : ℝ) = (order r : ℝ) - (order q : ℝ) := by
    dsimp [profileBinAge]
    rw [hSup, Nat.cast_sub hOrder]
  rw [← hAge] at hDecay
  have hRCount : profilePartSize P r ≤ dyadicProfileHistogram P d b := by
    rw [dyadicProfileHistogram_eq_part_sum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hrBin
  have hRReal : (profilePartSize P r : ℝ) ≤ dyadicProfileHistogram P d b := by exact_mod_cast hRCount
  exact hDecay.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hRReal (by norm_num)) (Real.exp_nonneg _))

theorem profile_bin_factorial_compression {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (P : RowProfile α ι) (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order)
    {d : ℕ} (hd : 0 < d) : ProfileBinFactorialCompression P d 4096 := by
  intro b
  by_cases hS : (dyadicProfileBinParts P d b).Nonempty
  · obtain ⟨q, hq⟩ := hS
    have hN : 0 < ∑ r ∈ dyadicProfileBinParts P d b, profilePartSize P r :=
      (profilePartSize_pos P q).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hq)
    have hTail : ∀ r ∈ dyadicProfileBinParts P d b, (profilePartSize P r : ℝ) ≤
        8 * (∑ s ∈ dyadicProfileBinParts P d b, profilePartSize P s : ℕ) *
          Real.exp (-(profileBinAge P order d b r : ℝ) / 4) := by
      intro r hr
      simpa only [dyadicProfileHistogram_eq_part_sum] using
        profile_bin_size_tail P order hGeometry hd b hr
    have h := four_family_factorial_compression (dyadicProfileBinParts P d b)
      (profileBinFamily P d) (profileBinAge P order d b)
      (profile_bin_code_injective P order hGeometry d b) (profilePartSize P) hN hTail
    rwa [← dyadicProfileHistogram_eq_part_sum] at h
  · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hS
    have hZero : dyadicProfileHistogram P d b = 0 := by
      rw [dyadicProfileHistogram_eq_part_sum, hEmpty, Finset.sum_empty]
    simp only [hEmpty, hZero, Nat.factorial_zero, Nat.cast_one,
      Nat.cast_zero, mul_zero, Real.exp_zero, mul_one, Finset.prod_empty, le_refl]

end CircularLaw
