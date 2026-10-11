import CircularLaw.ProfileBinCompression
import CircularLaw.ProfileSmallBinMass
import CircularLaw.CanonicalProfile

/-!
# Closed factorial compression for the canonical LLTTY profile

The creation-order geometry is supplied by the actual canonical partition.
The bin compression and its entropy consequences therefore require no
additional geometric or factorial-compression hypothesis.
-/

noncomputable section
open Classical
open scoped BigOperators Nat

namespace CircularLaw

def canonicalCreationOrder {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (q : CanonicalLabel y δ) : ℕ := q.val.2.val

def orderedCanonicalCreationOrder {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (q : Fin (Fintype.card (CanonicalLabel y δ))) : ℕ :=
  canonicalCreationOrder y δ (canonicalEnumeration y δ q)

theorem canonical_profile_order_geometry {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) :
    ProfileOrderGeometry (canonicalRowProfile y δ) (canonicalCreationOrder y δ) where
  injective := by
    intro q r h
    change (q.val.1, q.val.2.val) = (r.val.1, r.val.2.val) at h
    have hSpread : q.val.1 = r.val.1 := congrArg (fun z : Bool × ℕ => z.1) h
    have hOrder : q.val.2.val = r.val.2.val := congrArg (fun z : Bool × ℕ => z.2) h
    apply Subtype.ext
    exact Prod.ext hSpread (Fin.ext hOrder)
  lower q := (canonicalPart_size_height_source y δ q).1
  upper q := (canonicalPart_size_height_source y δ q).2

theorem orderedCanonical_profilePartSize_eq {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (q : Fin (Fintype.card (CanonicalLabel y δ))) :
    profilePartSize (orderedCanonicalRowProfile y δ) q =
      profilePartSize (canonicalRowProfile y δ) (canonicalEnumeration y δ q) := by
  unfold profilePartSize
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun _ => (canonicalEnumeration y δ).symm_apply_eq)

theorem orderedCanonical_profile_order_geometry {n : ℕ} (y : Fin n → ℂ) (δ : ℝ) :
    ProfileOrderGeometry (orderedCanonicalRowProfile y δ)
      (orderedCanonicalCreationOrder y δ) where
  injective := by
    intro q r h
    apply (canonicalEnumeration y δ).injective
    exact (canonical_profile_order_geometry y δ).injective h
  lower q := by
    rw [orderedCanonical_profilePartSize_eq]
    exact (canonical_profile_order_geometry y δ).lower (canonicalEnumeration y δ q)
  upper q := by
    rw [orderedCanonical_profilePartSize_eq]
    exact (canonical_profile_order_geometry y δ).upper (canonicalEnumeration y δ q)

theorem canonical_bin_factorial_compression {n : ℕ} (hn : 0 < n)
    (y : Fin n → ℂ) (δ : ℝ) {d : ℕ} (hd : 0 < d) :
    ProfileBinFactorialCompression (canonicalRowProfile y δ) d 4096 := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact profile_bin_factorial_compression _ _ (canonical_profile_order_geometry y δ) hd

theorem orderedCanonical_bin_factorial_compression {n : ℕ} (hn : 0 < n)
    (y : Fin n → ℂ) (δ : ℝ) {d : ℕ} (hd : 0 < d) :
    ProfileBinFactorialCompression (orderedCanonicalRowProfile y δ) d 4096 := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact profile_bin_factorial_compression _ _ (orderedCanonical_profile_order_geometry y δ) hd

theorem orderedCanonical_part_union_eq {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (S : Finset (Fin (Fintype.card (CanonicalLabel y δ)))) :
    Finset.univ.filter (fun a => (orderedCanonicalRowProfile y δ).part a ∈ S) =
      S.biUnion (fun q => taggedPart y δ (canonicalEnumeration y δ q).val) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
  constructor
  · intro hi
    refine ⟨(orderedCanonicalRowProfile y δ).part i, hi, ?_⟩
    simpa only [orderedCanonicalRowProfile, Equiv.apply_symm_apply] using
      canonicalCoordinateLabel_mem y δ i
  · rintro ⟨q, hq, hi⟩
    have hLabel := (canonicalCoordinateLabel_eq_iff y δ i (canonicalEnumeration y δ q)).mpr hi
    have hPart : (orderedCanonicalRowProfile y δ).part i = q := by
      change (canonicalEnumeration y δ).symm (canonicalCoordinateLabel y δ i) = q
      rw [hLabel, Equiv.symm_apply_apply]
    rwa [hPart]

theorem orderedCanonical_small_bin_mass {n : ℕ} (hn : 0 < n)
    (y : Fin n → ℂ) (δ : ℝ) {d : ℕ} (hd : 0 < d) (b : ℤ)
    (S : Finset (Fin (Fintype.card (CanonicalLabel y δ))))
    (hSubset : S ⊆ dyadicProfileBinParts (orderedCanonicalRowProfile y δ) d b)
    {T : ℝ} (hT : 0 ≤ T)
    (hSmall : ∀ q ∈ S, (profilePartSize (orderedCanonicalRowProfile y δ) q : ℝ) < T) :
    ((S.biUnion (fun q => taggedPart y δ (canonicalEnumeration y δ q).val)).card : ℝ) ≤
      512 * T := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : DecidableEq (Fin (Fintype.card (CanonicalLabel y δ))) := Classical.decEq _
  have h := profile_small_bin_mass (orderedCanonicalRowProfile y δ)
    (orderedCanonicalCreationOrder y δ) (orderedCanonical_profile_order_geometry y δ)
    hd b S hSubset hT hSmall
  refine le_trans ?_ h
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  obtain ⟨q, hq, hiq⟩ := Finset.mem_biUnion.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hLabel := (canonicalCoordinateLabel_eq_iff y δ i (canonicalEnumeration y δ q)).mpr hiq
  have hPart : (orderedCanonicalRowProfile y δ).part i = q := by
    change (canonicalEnumeration y δ).symm (canonicalCoordinateLabel y δ i) = q
    rw [hLabel, Equiv.symm_apply_apply]
  rwa [hPart]

theorem orderedCanonical_small_bin_cutoff {n : ℕ} (hn : 0 < n)
    (y : Fin n → ℂ) (δ : ℝ) {d : ℕ} (hd : 0 < d) (b : ℤ) (κ : ℝ)
    (S : Finset (Fin (Fintype.card (CanonicalLabel y δ))))
    (hSubset : S ⊆ dyadicProfileBinParts (orderedCanonicalRowProfile y δ) d b)
    (hSmall : ∀ q ∈ S, (profilePartSize (orderedCanonicalRowProfile y δ) q : ℝ) <
      Real.rpow (d : ℝ) (-κ) * n) :
    ((S.biUnion (fun q => taggedPart y δ (canonicalEnumeration y δ q).val)).card : ℝ) ≤
      512 * Real.rpow (d : ℝ) (-κ) * n := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := orderedCanonical_small_bin_mass hn y δ hd b S hSubset
    (mul_nonneg (Real.rpow_nonneg hdR.le _) (Nat.cast_nonneg n)) hSmall
  simpa only [mul_assoc] using h

theorem orderedCanonical_factorial_entropy {n : ℕ} [NeZero n]
    (y : Fin n → ℂ) (δ : ℝ) {d : ℕ} (hd : 0 < d) :
    ((n)! : ℝ) /
      (∏ q, ((profilePartSize (orderedCanonicalRowProfile y δ) q)! : ℝ)) ≤
        Real.exp (4096 * n + (n : ℝ) * (∑' b : ℤ,
          integerEntropyAtom (dyadicProfileLaw (orderedCanonicalRowProfile y δ) d) b)) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  simpa only [Fintype.card_fin] using profile_factorial_entropy
    (orderedCanonicalRowProfile y δ) d (orderedCanonical_bin_factorial_compression hn y δ hd)

theorem orderedCanonical_factorial_dispersion_cancel {n : ℕ} (hn : 0 < n)
    (y : Fin n → ℂ) (δ : ℝ) {d : ℕ} (hd : 0 < d)
    {c K : ℝ} (hc : 0 < c) (hK : (n : ℝ) / 2 ≤ K) :
    (((n)! : ℝ) /
      (∏ q, ((profilePartSize (orderedCanonicalRowProfile y δ) q)! : ℝ))) *
        Real.exp (-c * K * pairDispersion (fun a =>
          dyadicWeight (truncatedProfileWeight (orderedCanonicalRowProfile y δ) d
            ((orderedCanonicalRowProfile y δ).part a)))) ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 2)) * n) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hK' : (Fintype.card (Fin n) : ℝ) / 2 ≤ K := by simpa only [Fintype.card_fin] using hK
  simpa only [Fintype.card_fin] using profile_factorial_dispersion_cancel hc hK'
    (orderedCanonicalRowProfile y δ) d (orderedCanonical_bin_factorial_compression hn y δ hd)

end CircularLaw
