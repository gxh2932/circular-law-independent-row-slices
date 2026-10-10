import CircularLaw.LLYRowAction
import CircularLaw.LLYGradualAdjoint

/-!
# Gradual almost-constant invertibility on the actual retained rows

The retained set, coordinate blocks and product row-load events are
literal. In particular this applies when any single row is omitted.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem lly_gradual_almost_retained_norm_of_prefix {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hk₁Small : k₁ - 1 ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (I : Finset (Fin n)) (hRows : (99 / 100 : ℝ) * n ≤ I.card)
    (rows : RowSliceMatrix n d) (hLoad : LLYRowLoad I k₂ k₃ rows)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (x : EuclideanSpace ℂ (Fin n)) (hUnit : ‖x‖ = 1)
    (hGradual : (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃)
    (hAlmost : ¬sourceNonAlmostConstant δ ρ x) :
    2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁) ≤
      ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin x‖ := by
  obtain ⟨c, F, hMany, hClose⟩ := lly_unit_almost_constant_center hn hd hk₁ hk₃n
    hFit hDensity hRadius x hUnit hGradual hAlmost
  have hCenter := (lly_almost_center_bounds hk₃ hHalf (fun j => x j) F c hMany hClose).1
  have hGaps := lly_gradual_ordered_gaps (fun j => x j) hGradual
  have hB := lly_gradual_norm_constant_pos hn hd (r := r) (k₁ := k₁)
  have hNorm := lly_gradual_norm_bound hn hk₁ hFit x hGradual
  rw [hUnit] at hNorm
  have hCenterLower : 4 / (5 * llyGradualNormConstant n d r k₁) ≤ ‖c‖ := by
    apply (div_le_iff₀ (by positivity : 0 < 5 * llyGradualNormConstant n d r k₁)).mpr
    have h := mul_le_mul_of_nonneg_left hCenter hB.le
    nlinarith only [h, hNorm]
  let G := llyRowSurvivors I rows (fun j => x j) F k₁ k₂ k₃
  let H : Finset I := G.subtype (fun j => j ∈ I)
  have hHCard : H.card = G.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_eq_self.mpr (fun j hj => (llyRowSurvivors_mem hj).1)
  have hCard : (n : ℝ) / 3 ≤ H.card := by
    rw [hHCard]
    exact llyRowSurvivors_third_of_prefix I rows (fun j => x j) F hk₁n hk₂n hk₃n hk₁Small hMany hLoad hRows hScale₃
  let a := 4 * (d : ℝ) / (25 * llyGradualNormConstant n d r k₁)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hLarge : ∀ i ∈ H, a ≤ ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin x i‖ := by
    intro i hi
    have hiG : i.val ∈ G := Finset.mem_subtype.mp hi
    have hAction := lly_surviving_row_shifted_action hn hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n hk₂₃
      I rows x F c ζ i hGaps.2.1 hGaps.2.2 hCenter hClose hScale₂ hScale₃ hShift hiG
    have hC := mul_le_mul_of_nonneg_left hCenterLower (show 0 ≤ (d : ℝ) / 5 by positivity)
    have hALe : a ≤ (d : ℝ) / 5 * ‖c‖ := by
      dsimp only [a]
      convert hC using 1
      ring
    exact hALe.trans hAction
  have hEnergy := euclidean_subset_coordinates_energy_lower H
    ((retainedShiftedMatrix I ζ rows).toEuclideanLin x) ha hLarge
  have hCardEnergy := mul_le_mul_of_nonneg_right hCard (sq_nonneg a)
  have hTarget : (2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁)) ^ 2 =
      (n : ℝ) / 4 * a ^ 2 := by
    dsimp only [a]
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), div_pow]
    ring
  apply (sq_le_sq₀
    (show 0 ≤ 2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁) by positivity)
    (norm_nonneg ((retainedShiftedMatrix I ζ rows).toEuclideanLin x))).mp
  rw [hTarget]
  exact (show (n : ℝ) / 4 * a ^ 2 ≤ (n : ℝ) / 3 * a ^ 2 by
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg a)]).trans
      (hCardEnergy.trans hEnergy)

theorem lly_gradual_almost_retained_norm {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hk₁Small : k₁ ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (I : Finset (Fin n)) (hRows : (99 / 100 : ℝ) * n ≤ I.card)
    (rows : RowSliceMatrix n d) (hLoad : LLYRowLoad I k₂ k₃ rows)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (x : EuclideanSpace ℂ (Fin n)) (hUnit : ‖x‖ = 1)
    (hGradual : (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃)
    (hAlmost : ¬sourceNonAlmostConstant δ ρ x) :
    2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁) ≤
      ‖(retainedShiftedMatrix I ζ rows).toEuclideanLin x‖ := by
  exact lly_gradual_almost_retained_norm_of_prefix hn hd hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n hk₂₃
    hFit hHalf ((Nat.sub_le k₁ 1).trans hk₁Small) hScale₂ hScale₃ hDensity hRadius
    I hRows rows hLoad ζ hShift x hUnit hGradual hAlmost

theorem lly_gradual_almost_retained_kernel_exclusion_of_prefix {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hk₁Small : k₁ - 1 ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (I : Finset (Fin n)) (hRows : (99 / 100 : ℝ) * n ≤ I.card)
    (rows : RowSliceMatrix n d) (hLoad : LLYRowLoad I k₂ k₃ rows)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (x : EuclideanSpace ℂ (Fin n)) (hUnit : ‖x‖ = 1)
    (hGradual : (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃)
    (hAlmost : ¬sourceNonAlmostConstant δ ρ x) :
    (retainedShiftedMatrix I ζ rows).toEuclideanLin x ≠ 0 := by
  intro hZero
  have hLower := lly_gradual_almost_retained_norm_of_prefix hn hd hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n hk₂₃
    hFit hHalf hk₁Small hScale₂ hScale₃ hDensity hRadius I hRows rows hLoad ζ hShift x hUnit hGradual hAlmost
  rw [hZero, norm_zero] at hLower
  have hB := lly_gradual_norm_constant_pos hn hd (r := r) (k₁ := k₁)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hPositive : 0 < 2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁) := by positivity
  linarith

theorem lly_gradual_almost_retained_kernel_exclusion {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hk₁Small : k₁ ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (I : Finset (Fin n)) (hRows : (99 / 100 : ℝ) * n ≤ I.card)
    (rows : RowSliceMatrix n d) (hLoad : LLYRowLoad I k₂ k₃ rows)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (x : EuclideanSpace ℂ (Fin n)) (hUnit : ‖x‖ = 1)
    (hGradual : (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃)
    (hAlmost : ¬sourceNonAlmostConstant δ ρ x) :
    (retainedShiftedMatrix I ζ rows).toEuclideanLin x ≠ 0 := by
  exact lly_gradual_almost_retained_kernel_exclusion_of_prefix hn hd hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n hk₂₃
    hFit hHalf ((Nat.sub_le k₁ 1).trans hk₁Small) hScale₂ hScale₃ hDensity hRadius
    I hRows rows hLoad ζ hShift x hUnit hGradual hAlmost

end CircularLaw
