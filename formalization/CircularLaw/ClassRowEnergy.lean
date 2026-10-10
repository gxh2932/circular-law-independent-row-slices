import CircularLaw.CanonicalProfileStatistics

/-!
# Class energy at the actual retained row count

The class-size and entropy estimate is combined with the exact geometric
mean at `K=n-L` rows. The missing-row factor is explicit. Splitting the
dispersion exponent in half gives a common estimate for K2 and clustered
Pv; K1 retains the stronger height/weight product decay.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def canonicalClassRowEnergy {n : ℕ} (A : Set (Fin n → ℂ)) (y : Fin n → ℂ)
    (η : ℝ) (d K : ℕ) (c : ℝ) : ℝ :=
  let P := orderedCanonicalRowProfile y η
  (Nat.card (CoordinateMultisetClassIn A y) : ℝ) *
    profileGeometricMean P.part (truncatedProfileWeight P d) ^ K *
      Real.exp (-c * (K : ℝ) * profileCoordinateDispersion P d)

theorem profile_ratio_product_le_degree {n d : ℕ} {ι : Type*} [Fintype ι]
    (hn : 0 < n) (hd : 0 < d) (P : RowProfile (Fin n) ι) :
    (∏ q, ((P.height q : ℝ) / truncatedProfileWeight P d q) ^ profilePartSize P q) ≤
      (d : ℝ) ^ n := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hSum := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left (profile_height_weight_log_le_degree P hd q)
      (Nat.cast_nonneg (profilePartSize P q) : (0 : ℝ) ≤ _))
  have hTotal : (∑ q, (profilePartSize P q : ℝ)) = n := by
    change profileSelectedMass P Finset.univ = n
    rw [profileSelectedMass_total, Fintype.card_fin]
  rw [← Finset.sum_mul, hTotal] at hSum
  rw [profile_height_weight_product_eq_exp P hd]
  exact (Real.exp_le_exp.mpr hSum).trans_eq
    (by rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hd)])

theorem canonicalClassRowEnergy_product_bound {n d K L : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hRows : K + L = n)
    (A : Set (Fin n → ℂ)) (y : Fin n → ℂ) (η : ℝ) {c : ℝ}
    (hc : 0 < c) (hK : (n : ℝ) / 2 ≤ K) :
    let P := orderedCanonicalRowProfile y η
    canonicalClassRowEnergy A y η d K c ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 2)) * n) *
        (∏ q, ((P.height q : ℝ) / truncatedProfileWeight P d q) ^ profilePartSize P q) *
          ((n : ℝ) * Real.sqrt d) ^ L := by
  intro P
  let E := Real.exp (-c * (K : ℝ) * profileCoordinateDispersion P d)
  let R := ((n : ℝ) * Real.sqrt d) ^ L
  have hCost := orderedCanonical_profile_mean_row_cost hn hd hRows y η
  have hCount : 0 ≤ (Nat.card (CoordinateMultisetClassIn A y) : ℝ) := Nat.cast_nonneg _
  have hEnergy := orderedCanonicalClassIn_weighted_dispersion hn A y η hd hc hK
  calc
    canonicalClassRowEnergy A y η d K c ≤
      ((Nat.card (CoordinateMultisetClassIn A y) : ℝ) *
        ((∏ q, (truncatedProfileWeight P d q ^ profilePartSize P q)⁻¹) * R)) * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCost hCount) (Real.exp_nonneg _)
    _ = ((Nat.card (CoordinateMultisetClassIn A y) : ℝ) *
        (∏ q, (truncatedProfileWeight P d q ^ profilePartSize P q)⁻¹) * E) * R := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hEnergy
      (pow_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)) L)

theorem canonicalClassRowEnergy_split_bound {n d K L : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hRows : K + L = n)
    (A : Set (Fin n → ℂ)) (y : Fin n → ℂ) (η : ℝ) {c : ℝ}
    (hc : 0 < c) (hK : (n : ℝ) / 2 ≤ K) :
    let P := orderedCanonicalRowProfile y η
    canonicalClassRowEnergy A y η d K c ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 4)) * n) * (d : ℝ) ^ n *
        ((n : ℝ) * Real.sqrt d) ^ L *
          Real.exp (-(c / 2) * (K : ℝ) * profileCoordinateDispersion P d) := by
  intro P
  have hHalf := canonicalClassRowEnergy_product_bound hn hd hRows A y η (half_pos hc) hK
  rw [show c / 2 / 2 = c / 4 by ring] at hHalf
  have hRatio := profile_ratio_product_le_degree hn hd P
  have hPrefactor : canonicalClassRowEnergy A y η d K (c / 2) ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 4)) * n) * (d : ℝ) ^ n *
        ((n : ℝ) * Real.sqrt d) ^ L :=
    hHalf.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRatio (Real.exp_nonneg _))
      (pow_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)) L))
  have hSplit : canonicalClassRowEnergy A y η d K c =
      canonicalClassRowEnergy A y η d K (c / 2) *
        Real.exp (-(c / 2) * (K : ℝ) * profileCoordinateDispersion P d) := by
    have hExp : Real.exp (-c * (K : ℝ) * profileCoordinateDispersion P d) =
        Real.exp (-(c / 2) * (K : ℝ) * profileCoordinateDispersion P d) *
          Real.exp (-(c / 2) * (K : ℝ) * profileCoordinateDispersion P d) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp only [canonicalClassRowEnergy]
    rw [hExp]
    ring
  rw [hSplit]
  exact mul_le_mul_of_nonneg_right hPrefactor (Real.exp_nonneg _)

theorem canonicalClassRowEnergy_dispersion_lower_bound {n d K L : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hRows : K + L = n)
    (A : Set (Fin n → ℂ)) (y : Fin n → ℂ) (η : ℝ) {c g : ℝ}
    (hc : 0 < c) (hK : (n : ℝ) / 2 ≤ K)
    (hDispersion : g ≤ profileCoordinateDispersion (orderedCanonicalRowProfile y η) d) :
    canonicalClassRowEnergy A y η d K c ≤
      Real.exp ((4096 + entropyPenaltyConstant (c / 4)) * n) * (d : ℝ) ^ n *
        ((n : ℝ) * Real.sqrt d) ^ L * Real.exp (-(c / 2) * (K : ℝ) * g) := by
  apply (canonicalClassRowEnergy_split_bound hn hd hRows A y η hc hK).trans
  have hExponent := mul_le_mul_of_nonpos_left hDispersion
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (half_pos hc).le) (Nat.cast_nonneg K))
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExponent)
    (mul_nonneg (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (Nat.cast_nonneg d) n))
      (pow_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)) L))

theorem source_K1_class_row_energy {n d K L u : ℕ} {a₃ cK : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hRows : K + L = n)
    (ha : 0 < a₃) (haHalf : a₃ ≤ 1 / 2) (hcK : 0 ≤ cK) (hcKUpper : cK ≤ 1 / 4608)
    (hSize : 4 ≤ a₃ * (n : ℝ)) (A : Set (Fin n → ℂ))
    (x : Fin n → ℂ) (hx : x ∈ sourceSpreadFamily n d L a₃ cK u)
    (hK1 : (n : ℝ) - cK * (thirdSteepScale n a₃ : ℝ) / 4 ≤
      profileSelectedMass (sourceScaleProfile d u x)
        (profileCutoffParts (sourceScaleProfile d u x) d (cK * a₃ / 16)))
    {c : ℝ} (hc : 0 < c) (hK : (n : ℝ) / 2 ≤ K) :
    canonicalClassRowEnergy A (fun i => canonicalApprox (d ^ u) (x i))
      ((d : ℝ) / (d ^ u : ℕ)) d K c ≤
    Real.exp ((4096 + entropyPenaltyConstant (c / 2)) * n) *
      Real.rpow (d : ℝ) (-(cK * a₃ / 32) * n) * ((n : ℝ) * Real.sqrt d) ^ L := by
  apply (canonicalClassRowEnergy_product_bound hn hd hRows A
    (fun i => canonicalApprox (d ^ u) (x i)) ((d : ℝ) / (d ^ u : ℕ)) hc hK).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (source_K1_product_bound hn hd ha haHalf hcK hcKUpper hSize x hx hK1)
      (Real.exp_nonneg _))
    (pow_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)) L)

end CircularLaw
