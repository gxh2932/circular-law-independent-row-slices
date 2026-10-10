import CircularLaw.LLYColumnAction

/-!
# Actual adjoint exclusion for unit gradual almost-constant vectors

The proved gradual norm constant is used throughout. The conclusion
keeps all rank, radius and spectral-shift budgets explicit.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem euclidean_subset_coordinates_energy_lower {ι : Type*} [Fintype ι]
    (G : Finset ι) (v : EuclideanSpace ℂ ι) {a : ℝ} (ha : 0 ≤ a)
    (hLarge : ∀ i ∈ G, a ≤ ‖v i‖) : (G.card : ℝ) * a ^ 2 ≤ ‖v‖ ^ 2 := by
  calc
    _ = ∑ _i ∈ G, a ^ 2 := by simp
    _ ≤ ∑ i ∈ G, ‖v i‖ ^ 2 := Finset.sum_le_sum (fun i hi =>
      (sq_le_sq₀ ha (norm_nonneg _)).mpr (hLarge i hi))
    _ ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => sq_nonneg ‖v i‖)
    _ = _ := (EuclideanSpace.norm_sq_eq v).symm

theorem lly_gradual_almost_adjoint_norm_of_prefix {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hTop : (d : ℝ) * (k₁ - 1 : ℕ) ≤ (n : ℝ) / 9)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (rows : RowSliceMatrix n d) (hColumns : RowSliceColumnLowerBound (5 * (d : ℝ) / 6) rows)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (x : EuclideanSpace ℂ (Fin n)) (hUnit : ‖x‖ = 1)
    (hGradual : (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃)
    (hAlmost : ¬sourceNonAlmostConstant δ ρ x) :
    2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁) ≤
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ := by
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
  let G := llyColumnSurvivors rows (fun j => x j) F k₁ k₂ k₃
  have hCard : (n : ℝ) / 2 ≤ G.card := llyColumnSurvivors_half_of_prefix hn hd hk₂ hk₃ hk₁n hk₂n hk₃n
    rows (fun j => x j) F hMany hTop hScale₃
  let a := 4 * (d : ℝ) / (25 * llyGradualNormConstant n d r k₁)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hLarge : ∀ j ∈ G, a ≤ ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x j‖ := by
    intro j hj
    have hAction := lly_surviving_column_adjoint_action hn hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n hk₂₃
      rows x F c ζ j hGaps.2.1 hGaps.2.2 hCenter hClose hScale₂ hScale₃ (hColumns j) hShift hj
    have hC := mul_le_mul_of_nonneg_left hCenterLower (show 0 ≤ (d : ℝ) / 5 by positivity)
    have hALe : a ≤ (d : ℝ) / 5 * ‖c‖ := by
      dsimp only [a]
      convert hC using 1
      ring
    exact hALe.trans hAction
  have hEnergy := euclidean_subset_coordinates_energy_lower G
    ((fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x) ha hLarge
  have hCardEnergy := mul_le_mul_of_nonneg_right hCard (sq_nonneg a)
  have hTarget : (2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁)) ^ 2 =
      (n : ℝ) / 4 * a ^ 2 := by
    dsimp only [a]
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), div_pow]
    ring
  apply (sq_le_sq₀
    (show 0 ≤ 2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁) by positivity)
    (norm_nonneg ((fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x))).mp
  rw [hTarget]
  apply (show (n : ℝ) / 4 * a ^ 2 ≤ (n : ℝ) / 2 * a ^ 2 by
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg a)]).trans
      (hCardEnergy.trans hEnergy)

theorem lly_gradual_almost_adjoint_norm {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hTop : (d : ℝ) * k₁ ≤ (n : ℝ) / 9)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (rows : RowSliceMatrix n d) (hColumns : RowSliceColumnLowerBound (5 * (d : ℝ) / 6) rows)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (x : EuclideanSpace ℂ (Fin n)) (hUnit : ‖x‖ = 1)
    (hGradual : (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃)
    (hAlmost : ¬sourceNonAlmostConstant δ ρ x) :
    2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁) ≤
      ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ := by
  apply lly_gradual_almost_adjoint_norm_of_prefix hn hd hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n hk₂₃
    hFit hHalf ?_ hScale₂ hScale₃ hDensity hRadius rows hColumns ζ hShift x hUnit hGradual hAlmost
  have hRank : ((k₁ - 1 : ℕ) : ℝ) ≤ k₁ := by exact_mod_cast Nat.sub_le k₁ 1
  exact (mul_le_mul_of_nonneg_left hRank (Nat.cast_nonneg d)).trans hTop

def llyGradualAlmostAdjointFailure {n d : ℕ} (ζ : ℂ) (rows : RowSliceMatrix n d)
    (ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
    (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
    ‖(fullShiftedSliceMatrix ζ rows).conjTranspose.toEuclideanLin x‖ ≤ τ

theorem lly_gradual_almost_adjoint_failure_probability_of_prefix {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hTop : (d : ℝ) * (k₁ - 1 : ℕ) ≤ (n : ℝ) / 9)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ τ : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (hThreshold : τ < 2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁))
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llyGradualAlmostAdjointFailure ζ rows ℓ r k₁ k₂ k₃ δ ρ τ) ≤
      (n : ℝ) * Real.exp (-(d : ℝ) / 72) := by
  apply (uniformProbability_mono ?_).trans (square_rowSliceColumn_lower_failure hn hdn)
  intro rows hFail hColumns
  obtain ⟨x, hUnit, hAlmost, hGradual, hSmall⟩ := hFail
  have hLower := lly_gradual_almost_adjoint_norm_of_prefix hn hd hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n hk₂₃
    hFit hHalf hTop hScale₂ hScale₃ hDensity hRadius rows hColumns ζ hShift x hUnit hGradual hAlmost
  exact not_lt_of_ge (hLower.trans hSmall) hThreshold

theorem lly_gradual_almost_adjoint_failure_probability {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hTop : (d : ℝ) * k₁ ≤ (n : ℝ) / 9)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ τ : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (hThreshold : τ < 2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁))
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25) :
    uniformProbability (fun rows : RowSliceMatrix n d =>
      llyGradualAlmostAdjointFailure ζ rows ℓ r k₁ k₂ k₃ δ ρ τ) ≤
      (n : ℝ) * Real.exp (-(d : ℝ) / 72) := by
  apply lly_gradual_almost_adjoint_failure_probability_of_prefix hn hd hdn hk₁ hk₂ hk₃
    hk₁n hk₂n hk₃n hk₂₃ hFit hHalf ?_ hScale₂ hScale₃ hDensity hRadius hThreshold ζ hShift
  have hRank : ((k₁ - 1 : ℕ) : ℝ) ≤ k₁ := by exact_mod_cast Nat.sub_le k₁ 1
  exact (mul_le_mul_of_nonneg_left hRank (Nat.cast_nonneg d)).trans hTop

end CircularLaw
