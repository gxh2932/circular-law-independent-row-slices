import CircularLaw.ProfileBinCompression

/-!
# Total mass of small parts within one dyadic bin

The largest creation order is chosen separately within each of the four
families of the selected subset. This preserves the size cutoff and gives
the source small-bin estimate for arbitrary subsets of small parts.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def profileSubsetMaxOrder {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (order : ι → ℕ) (d : ℕ) (S : Finset ι) (family : Bool × Bool) : ℕ :=
  (S.filter (fun q => profileBinFamily P d q = family)).sup order

def profileSubsetAge {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (order : ι → ℕ) (d : ℕ) (S : Finset ι) (q : ι) : ℕ :=
  profileSubsetMaxOrder P order d S (profileBinFamily P d q) - order q

theorem profile_subset_order_le_max {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (order : ι → ℕ) (d : ℕ) (S : Finset ι)
    {q : ι} (hq : q ∈ S) :
    order q ≤ profileSubsetMaxOrder P order d S (profileBinFamily P d q) :=
  Finset.le_sup (Finset.mem_filter.mpr ⟨hq, rfl⟩)

theorem profile_subset_code_injective {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order)
    (d : ℕ) (S : Finset ι) :
    Set.InjOn (fun q => (profileBinFamily P d q, (profileSubsetAge P order d S q : ℤ)))
      (S : Set ι) := by
  intro q hq r hr hCode
  have hFamily : profileBinFamily P d q = profileBinFamily P d r :=
    congrArg Prod.fst hCode
  have hCastAge : (profileSubsetAge P order d S q : ℤ) =
      (profileSubsetAge P order d S r : ℤ) := congrArg Prod.snd hCode
  have hAge : profileSubsetAge P order d S q = profileSubsetAge P order d S r := by
    exact_mod_cast hCastAge
  have hQ := profile_subset_order_le_max P order d S hq
  have hR := profile_subset_order_le_max P order d S hr
  have hMax : profileSubsetMaxOrder P order d S (profileBinFamily P d q) =
      profileSubsetMaxOrder P order d S (profileBinFamily P d r) := congrArg _ hFamily
  have hOrder : order q = order r := by
    dsimp [profileSubsetAge] at hAge
    omega
  have hSpread : P.spread q = P.spread r := congrArg Prod.fst hFamily
  exact hGeometry.injective (Prod.ext hSpread hOrder)

theorem profile_subset_cutoff_tail {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (P : RowProfile α ι) (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order)
    {d : ℕ} (hd : 0 < d) (b : ℤ) (S : Finset ι)
    (hSubset : S ⊆ dyadicProfileBinParts P d b) {T : ℝ}
    (hSmall : ∀ r ∈ S, (profilePartSize P r : ℝ) < T) {q : ι} (hq : q ∈ S) :
    (profilePartSize P q : ℝ) ≤ 8 * T * Real.exp (-(profileSubsetAge P order d S q : ℝ) / 4) := by
  have hNonempty : (S.filter (fun r => profileBinFamily P d r = profileBinFamily P d q)).Nonempty :=
    ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩⟩
  obtain ⟨r, hr, hSup⟩ := Finset.exists_mem_eq_sup _ hNonempty order
  change profileSubsetMaxOrder P order d S (profileBinFamily P d q) = order r at hSup
  have hrS := (Finset.mem_filter.mp hr).1
  have hFamily := (Finset.mem_filter.mp hr).2
  have hOrder := (profile_subset_order_le_max P order d S hq).trans_eq hSup
  have hBin : dyadicProfilePartOrder P d q = dyadicProfilePartOrder P d r :=
    (Finset.mem_filter.mp (hSubset hq)).2.trans (Finset.mem_filter.mp (hSubset hrS)).2.symm
  have hDecay := profile_same_family_size_decay P order hGeometry hd hFamily.symm hBin hOrder
  have hAge : (profileSubsetAge P order d S q : ℝ) = (order r : ℝ) - (order q : ℝ) := by
    dsimp [profileSubsetAge]
    rw [hSup, Nat.cast_sub hOrder]
  rw [← hAge] at hDecay
  exact hDecay.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hSmall r hrS).le (by norm_num)) (Real.exp_nonneg _))

theorem profile_small_bin_sum {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (P : RowProfile α ι) (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order)
    {d : ℕ} (hd : 0 < d) (b : ℤ) (S : Finset ι)
    (hSubset : S ⊆ dyadicProfileBinParts P d b) {T : ℝ} (hT : 0 ≤ T)
    (hSmall : ∀ q ∈ S, (profilePartSize P q : ℝ) < T) :
    (∑ q ∈ S, profilePartSize P q : ℕ) ≤ (512 : ℝ) * T := by
  have hE := four_family_exponential_sum S (profileBinFamily P d)
    (profileSubsetAge P order d S) (profile_subset_code_injective P order hGeometry d S)
    (α := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  norm_num at hE
  have hE' : (∑ q ∈ S, Real.exp (-(profileSubsetAge P order d S q : ℝ) / 4)) ≤ 64 := by
    convert hE using 1
    apply Finset.sum_congr rfl
    intro q _
    congr 1
    ring
  calc
    (∑ q ∈ S, profilePartSize P q : ℕ) = ∑ q ∈ S, (profilePartSize P q : ℝ) := by
      exact_mod_cast (Nat.cast_sum S (profilePartSize P) :
        (↑(∑ q ∈ S, profilePartSize P q) : ℝ) = _)
    _ ≤ ∑ q ∈ S, 8 * T * Real.exp (-(profileSubsetAge P order d S q : ℝ) / 4) :=
      Finset.sum_le_sum (fun q hq => profile_subset_cutoff_tail P order hGeometry hd b S hSubset hSmall hq)
    _ = 8 * T * ∑ q ∈ S, Real.exp (-(profileSubsetAge P order d S q : ℝ) / 4) := by
      rw [Finset.mul_sum]
    _ ≤ 8 * T * 64 := mul_le_mul_of_nonneg_left hE' (mul_nonneg (by norm_num) hT)
    _ = 512 * T := by ring

theorem profile_part_union_card {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (S : Finset ι) :
    (Finset.univ.filter (fun a => P.part a ∈ S)).card = ∑ q ∈ S, profilePartSize P q := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset α) S P.part
  simpa only [profilePartSize, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.mem_univ, true_and] using h.symm

theorem profile_small_bin_mass {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (P : RowProfile α ι) (order : ι → ℕ) (hGeometry : ProfileOrderGeometry P order)
    {d : ℕ} (hd : 0 < d) (b : ℤ) (S : Finset ι)
    (hSubset : S ⊆ dyadicProfileBinParts P d b) {T : ℝ} (hT : 0 ≤ T)
    (hSmall : ∀ q ∈ S, (profilePartSize P q : ℝ) < T) :
    ((Finset.univ.filter (fun a => P.part a ∈ S)).card : ℝ) ≤ 512 * T := by
  rw [profile_part_union_card]
  exact profile_small_bin_sum P order hGeometry hd b S hSubset hT hSmall

end CircularLaw
