import CircularLaw.RepeatedValueWeight
import CircularLaw.ProfileRange

/-!
# Exact geometric-mean powers and the missing-row cost

The exponent `n` gives precisely the product of inverse weights to their
part sizes. Passing to `K=n-L` rows costs at most `(n*sqrt(d))^L` for
the actual canonical profile. No height or mean bound remains assumed
in that specialization.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem profileGeometricMean_pos {α ι : Type*} [Fintype α] [Fintype ι]
    (part : α → ι) (w : ι → ℝ) (hw : ∀ q, 0 < w q) :
    0 < profileGeometricMean part w := by
  rw [profileGeometricMean_eq_exp part w hw]
  exact Real.exp_pos _

theorem partMass_mul_dimension {n : ℕ} {ι : Type*} (hn : 0 < n)
    (P : RowProfile (Fin n) ι) (q : ι) :
    partMass P.part q * n = profilePartSize P q := by
  rw [partMass_eq_profile_size, Fintype.card_fin]
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)

theorem profileGeometricMean_pow_dimension {n : ℕ} {ι : Type*} [Fintype ι]
    (hn : 0 < n) (P : RowProfile (Fin n) ι) (w : ι → ℝ) (hw : ∀ q, 0 < w q) :
    profileGeometricMean P.part w ^ n = ∏ q, (w q ^ profilePartSize P q)⁻¹ := by
  unfold profileGeometricMean
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro q _
  have hPow : Real.rpow (w q) ((-partMass P.part q) * (n : ℝ)) =
      Real.rpow (w q) (-partMass P.part q) ^ n :=
    (Real.rpow_mul (hw q).le _ _).trans (Real.rpow_natCast _ n)
  rw [← hPow, show (-partMass P.part q) * (n : ℝ) = -(profilePartSize P q : ℝ) by
    nlinarith only [partMass_mul_dimension hn P q]]
  have hNeg : Real.rpow (w q) (-(profilePartSize P q : ℝ)) =
      (w q ^ profilePartSize P q)⁻¹ := by
    simpa only [Real.rpow_natCast] using Real.rpow_neg (hw q).le (profilePartSize P q : ℝ)
  exact hNeg

theorem profileGeometricMean_lower_inv_upper {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (part : α → ι) (w : ι → ℝ) (hw : ∀ q, 0 < w q)
    {R : ℝ} (hR : 0 < R) (hUpper : ∀ q, w q ≤ R) :
    R⁻¹ ≤ profileGeometricMean part w := by
  have hMean : finiteMean (fun a => Real.log (w (part a))) ≤ Real.log R := by
    have h := finiteMean_mono (fun a => Real.log_le_log (hw (part a)) (hUpper (part a)))
    simpa only [finiteMean_const] using h
  calc
    _ = Real.exp (-Real.log R) := by rw [Real.exp_neg, Real.exp_log hR]
    _ ≤ _ := by
      rw [profileGeometricMean_eq_exp part w hw]
      exact Real.exp_le_exp.mpr (neg_le_neg hMean)

theorem profileGeometricMean_pow_rows {n K L : ℕ} {ι : Type*} [Fintype ι]
    (hn : 0 < n) (P : RowProfile (Fin n) ι) (w : ι → ℝ) (hw : ∀ q, 0 < w q)
    (hRows : K + L = n) :
    profileGeometricMean P.part w ^ K =
      (∏ q, (w q ^ profilePartSize P q)⁻¹) * (profileGeometricMean P.part w ^ L)⁻¹ := by
  have hW : 0 < profileGeometricMean P.part w := profileGeometricMean_pos _ _ hw
  rw [← div_eq_mul_inv]
  apply (eq_div_iff (pow_pos hW L).ne').mpr
  rw [← pow_add, hRows, profileGeometricMean_pow_dimension hn P w hw]

theorem profileGeometricMean_row_cost {n K L : ℕ} {ι : Type*} [Fintype ι]
    (hn : 0 < n) (P : RowProfile (Fin n) ι) (w : ι → ℝ) (hw : ∀ q, 0 < w q)
    (hRows : K + L = n) {R : ℝ} (hR : 0 < R) (hUpper : ∀ q, w q ≤ R) :
    profileGeometricMean P.part w ^ K ≤ (∏ q, (w q ^ profilePartSize P q)⁻¹) * R ^ L := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hW := profileGeometricMean_pos P.part w hw
  have hLower := profileGeometricMean_lower_inv_upper P.part w hw hR hUpper
  have hPow : (R ^ L)⁻¹ ≤ profileGeometricMean P.part w ^ L := by
    simpa only [inv_pow] using pow_le_pow_left₀ (inv_nonneg.mpr hR.le) hLower L
  have hInv := (inv_le_inv₀ (pow_pos hW L) (inv_pos.mpr (pow_pos hR L))).mpr hPow
  rw [inv_inv] at hInv
  rw [profileGeometricMean_pow_rows hn P w hw hRows]
  exact mul_le_mul_of_nonneg_left hInv
    (Finset.prod_nonneg (fun q _ => inv_nonneg.mpr (pow_nonneg (hw q).le _)))

theorem orderedCanonical_profile_mean_row_cost {n K L d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hRows : K + L = n) (y : Fin n → ℂ) (η : ℝ) :
    let P := orderedCanonicalRowProfile y η
    profileGeometricMean P.part (truncatedProfileWeight P d) ^ K ≤
      (∏ q, (truncatedProfileWeight P d q ^ profilePartSize P q)⁻¹) *
        ((n : ℝ) * Real.sqrt d) ^ L := by
  intro P
  apply profileGeometricMean_row_cost hn P _ (truncatedProfileWeight_pos P hd) hRows
    (mul_pos (by exact_mod_cast hn) (Real.sqrt_pos.mpr (by exact_mod_cast hd)))
  intro q
  simpa only [Fintype.card_fin] using (truncatedProfileWeight_bounds P hd q
    (by simpa only [Fintype.card_fin] using orderedCanonicalRowProfile_height_le y η q)).2

end CircularLaw
