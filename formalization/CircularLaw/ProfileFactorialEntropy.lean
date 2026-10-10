import CircularLaw.DyadicHistogramEntropy

/-!
# Part factorials, dyadic-bin factorials, and entropy

This file proves the global product consequence of local factorial
compression and the resulting source entropy/cancellation inequalities.
The actual canonical profile supplies that input in `CanonicalBinCompression`.
-/

noncomputable section
open Classical
open scoped BigOperators Nat ENNReal

namespace CircularLaw

def profilePartSize {α ι : Type*} [Fintype α] (P : RowProfile α ι) (q : ι) : ℕ :=
  Nat.card {a : α // P.part a = q}

def dyadicProfilePartOrder {α ι : Type*} [Fintype α] (P : RowProfile α ι)
    (d : ℕ) (q : ι) : ℤ := Int.floor (Real.logb 2 (truncatedProfileWeight P d q))

def dyadicProfileBinParts {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (d : ℕ) (b : ℤ) : Finset ι :=
  Finset.univ.filter (fun q => dyadicProfilePartOrder P d q = b)

theorem dyadicProfilePartOrder_mem_histogram {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (d : ℕ) (q : ι) :
    dyadicProfilePartOrder P d q ∈ dyadicProfileHistogramSupport P d := by
  obtain ⟨a, ha⟩ := P.part_surjective q
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, by
    simp only [dyadicProfilePartOrder, ha]⟩

theorem dyadicProfileHistogram_eq_part_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (d : ℕ) (b : ℤ) :
    dyadicProfileHistogram P d b = ∑ q ∈ dyadicProfileBinParts P d b, profilePartSize P q := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset α) (dyadicProfileBinParts P d b) P.part
  rw [dyadicProfileHistogram, integerHistogram_eq_filter_card]
  simpa only [profilePartSize, Nat.card_eq_fintype_card, Fintype.card_subtype,
    dyadicProfileBinParts, dyadicProfilePartOrder, Finset.mem_filter,
    Finset.mem_univ, true_and] using h.symm

theorem profile_part_factorial_pos {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) : (0 : ℝ) < ∏ q, ((profilePartSize P q)! : ℝ) :=
  Finset.prod_pos (fun q _ => by exact_mod_cast Nat.factorial_pos (profilePartSize P q))

theorem dyadic_histogram_factorial_pos {α ι : Type*} [Fintype α]
    (P : RowProfile α ι) (d : ℕ) :
    (0 : ℝ) < ∏ b ∈ dyadicProfileHistogramSupport P d, ((dyadicProfileHistogram P d b)! : ℝ) :=
  Finset.prod_pos (fun b _ => by exact_mod_cast Nat.factorial_pos (dyadicProfileHistogram P d b))

theorem profile_factorial_product_by_bins {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (d : ℕ) :
    (∏ b ∈ dyadicProfileHistogramSupport P d,
      ∏ q ∈ dyadicProfileBinParts P d b, ((profilePartSize P q)! : ℝ)) =
        ∏ q, ((profilePartSize P q)! : ℝ) := by
  exact Finset.prod_fiberwise_of_maps_to
    (fun q _ => dyadicProfilePartOrder_mem_histogram P d q) _

/-- The exact local estimate in `eq:factorial-compression`, supplied for
canonical LLTTY parts by `CanonicalBinCompression`. -/
def ProfileBinFactorialCompression {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (d : ℕ) (C : ℝ) : Prop :=
  ∀ b : ℤ, ((dyadicProfileHistogram P d b)! : ℝ) *
      Real.exp (-C * dyadicProfileHistogram P d b) ≤
    ∏ q ∈ dyadicProfileBinParts P d b, ((profilePartSize P q)! : ℝ)

theorem profile_factorial_compression_global {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (d : ℕ) {C : ℝ} (hCompression : ProfileBinFactorialCompression P d C) :
    (∏ b ∈ dyadicProfileHistogramSupport P d, ((dyadicProfileHistogram P d b)! : ℝ)) *
        Real.exp (-C * Fintype.card α) ≤ ∏ q, ((profilePartSize P q)! : ℝ) := by
  have h := Finset.prod_le_prod
    (fun b (_ : b ∈ dyadicProfileHistogramSupport P d) =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _))
    (fun b _ => hCompression b)
  rw [profile_factorial_product_by_bins] at h
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum,
    ← Nat.cast_sum, dyadicProfileHistogram_total] at h
  exact h

theorem profile_factorial_ratio_by_bins {α ι : Type*} [Fintype α] [Fintype ι]
    (P : RowProfile α ι) (d : ℕ) {C : ℝ} (hCompression : ProfileBinFactorialCompression P d C) :
    ((Fintype.card α)! : ℝ) / (∏ q, ((profilePartSize P q)! : ℝ)) ≤
      Real.exp (C * Fintype.card α) *
        (((Fintype.card α)! : ℝ) /
          (∏ b ∈ dyadicProfileHistogramSupport P d, ((dyadicProfileHistogram P d b)! : ℝ))) := by
  have hBinPos := dyadic_histogram_factorial_pos P d
  have hProduct := profile_factorial_compression_global P d hCompression
  have hNum : (0 : ℝ) ≤ (Fintype.card α)! := Nat.cast_nonneg _
  calc
    _ ≤ ((Fintype.card α)! : ℝ) /
        ((∏ b ∈ dyadicProfileHistogramSupport P d, ((dyadicProfileHistogram P d b)! : ℝ)) *
          Real.exp (-C * Fintype.card α)) :=
      div_le_div_of_nonneg_left hNum (mul_pos hBinPos (Real.exp_pos _)) hProduct
    _ = _ := by
      rw [show -C * (Fintype.card α : ℝ) = -(C * Fintype.card α) by ring, Real.exp_neg]
      field_simp

theorem profile_factorial_entropy {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    [MeasurableSpace α] [MeasurableSingletonClass α] (P : RowProfile α ι) (d : ℕ)
    {C : ℝ} (hCompression : ProfileBinFactorialCompression P d C) :
    ((Fintype.card α)! : ℝ) / (∏ q, ((profilePartSize P q)! : ℝ)) ≤
      Real.exp (C * Fintype.card α + (Fintype.card α : ℝ) *
        (∑' b : ℤ, integerEntropyAtom (dyadicProfileLaw P d) b)) := by
  calc
    _ ≤ Real.exp (C * Fintype.card α) *
        (((Fintype.card α)! : ℝ) /
          (∏ b ∈ dyadicProfileHistogramSupport P d, ((dyadicProfileHistogram P d b)! : ℝ))) :=
      profile_factorial_ratio_by_bins P d hCompression
    _ ≤ Real.exp (C * Fintype.card α) * Real.exp ((Fintype.card α : ℝ) *
        (∑' b : ℤ, integerEntropyAtom (dyadicProfileLaw P d) b)) :=
      mul_le_mul_of_nonneg_left (dyadic_histogram_factorial_entropy P d) (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

theorem profile_factorial_dispersion_cancel {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    [MeasurableSpace α] [MeasurableSingletonClass α] {c K C : ℝ}
    (hc : 0 < c) (hK : (Fintype.card α : ℝ) / 2 ≤ K) (P : RowProfile α ι) (d : ℕ)
    (hCompression : ProfileBinFactorialCompression P d C) :
    (((Fintype.card α)! : ℝ) / (∏ q, ((profilePartSize P q)! : ℝ))) *
        Real.exp (-c * K *
          pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P d (P.part a)))) ≤
      Real.exp ((C + entropyPenaltyConstant (c / 2)) * Fintype.card α) :=
  dyadic_profile_compression_cancel hc (Nat.cast_nonneg _) hK P d
    (profile_factorial_entropy P d hCompression)

end CircularLaw
