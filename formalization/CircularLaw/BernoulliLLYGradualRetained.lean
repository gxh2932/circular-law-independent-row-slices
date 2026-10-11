import CircularLaw.BernoulliLLYRowAction
import CircularLaw.LLYGradualAdjoint

/-!
# Gradual almost-constant exclusion for actual retained Bernoulli rows

The deterministic norm lower bound uses the actual row-degree and load
events. Their checked probabilities supply the entire gradual branch.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

theorem bernoulli_lly_gradual_almost_retained_norm_of_prefix {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hPrefix : k₁ - 1 ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (I : Finset (Fin n)) (hRows : (99 / 100 : ℝ) * n ≤ I.card)
    (sample : BernoulliSquareSample n)
    (hDegree : BernoulliRowDegreeLowerBound (9 * (d : ℝ) / 10) sample)
    (hLoad : BernoulliLLYRowLoad d I k₂ k₃ sample)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25)
    (x : EuclideanSpace ℂ (Fin n)) (hUnit : ‖x‖ = 1)
    (hGradual : (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃)
    (hAlmost : ¬sourceNonAlmostConstant δ ρ x) :
    2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁) ≤
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x‖ := by
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
  let G := bernoulliLLYRowSurvivors d I sample (fun j => x j) F k₁ k₂ k₃
  let H : Finset I := G.subtype (fun j => j ∈ I)
  have hHCard : H.card = G.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_eq_self.mpr (fun j hj => (bernoulli_lly_row_survivors_mem hj).1)
  have hCard : (n : ℝ) / 3 ≤ H.card := by
    rw [hHCard]
    exact bernoulli_lly_row_survivors_third_of_prefix I sample (fun j => x j) F
      hk₁n hk₂n hk₃n hPrefix hMany hLoad hRows hScale₃
  let a := 4 * (d : ℝ) / (25 * llyGradualNormConstant n d r k₁)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hLarge : ∀ i ∈ H, a ≤ ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x i‖ := by
    intro i hi
    have hiG : i.val ∈ G := Finset.mem_subtype.mp hi
    have hAction := bernoulli_lly_surviving_row_shifted_action hn hk₁ hk₂ hk₃ hk₁n hk₂n hk₃n hk₂₃
      I sample x F c ζ i hGaps.2.1 hGaps.2.2 hCenter hClose hScale₂ hScale₃ hDegree hShift hiG
    have hC := mul_le_mul_of_nonneg_left hCenterLower (show 0 ≤ (d : ℝ) / 5 by positivity)
    have hALe : a ≤ (d : ℝ) / 5 * ‖c‖ := by
      dsimp only [a]
      convert hC using 1
      ring
    exact hALe.trans hAction
  have hEnergy := euclidean_subset_coordinates_energy_lower H
    ((retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x) ha hLarge
  have hCardEnergy := mul_le_mul_of_nonneg_right hCard (sq_nonneg a)
  have hTarget : (2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁)) ^ 2 =
      (n : ℝ) / 4 * a ^ 2 := by
    dsimp only [a]
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), div_pow]
    ring
  apply (sq_le_sq₀
    (show 0 ≤ 2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁) by positivity)
    (norm_nonneg ((retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x))).mp
  rw [hTarget]
  exact (show (n : ℝ) / 4 * a ^ 2 ≤ (n : ℝ) / 3 * a ^ 2 by
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg a)]).trans
      (hCardEnergy.trans hEnergy)

def BernoulliLLYGradualAlmostRetainedFailure {n : ℕ}
    (I : Finset (Fin n)) (ζ : ℂ) (sample : BernoulliSquareSample n)
    (d ℓ r k₁ k₂ k₃ : ℕ) (δ ρ τ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ ¬sourceNonAlmostConstant δ ρ x ∧
    (fun j => x j) ∉ llySteepUnion d ℓ r k₁ k₂ k₃ ∧
    ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin x‖ ≤ τ

theorem bernoulli_lly_gradual_almost_retained_failure_probability {n d ℓ r k₁ k₂ k₃ : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ≤ n)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    (hk₁n : k₁ ≤ n) (hk₂n : k₂ ≤ n) (hk₃n : k₃ ≤ n) (hk₂₃ : k₂ ≤ k₃)
    (hFit : k₁ ≤ ℓ ^ (r + 1)) (hHalf : 2 * k₃ ≤ n)
    (hPrefix : k₁ - 1 ≤ almostConstantRank n d)
    (hScale₂ : (k₂ : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 1000)
    (hScale₃ : (k₃ : ℝ) ≤ (n : ℝ) / 1000) {δ ρ τ a : ℝ}
    (hDensity : δ * n ≤ k₃) (hRadius : ρ ≤ Real.sqrt n / (5 * llyGradualNormConstant n d r k₁))
    (hThreshold : τ < 2 * (d : ℝ) * Real.sqrt n / (25 * llyGradualNormConstant n d r k₁))
    (ha : 0 < a) (haOne : a ≤ 1) (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n)
    (hEntropy0 : smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4)
    (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4)
    (hDimension : 4 * Real.log 4 ≤ rowLoadRate * n)
    (I : Finset (Fin n)) (hRows : (99 / 100 : ℝ) * n ≤ I.card)
    (ζ : ℂ) (hShift : ‖ζ‖ ≤ 4 * (d : ℝ) / 25) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      BernoulliLLYGradualAlmostRetainedFailure I ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} ≤
      (n : ℝ) * Real.exp (-(d : ℝ) / 200) + Real.exp (-(rowLoadRate / 4) * n) := by
  have hSubset : {sample : BernoulliSquareSample n |
      BernoulliLLYGradualAlmostRetainedFailure I ζ sample d ℓ r k₁ k₂ k₃ δ ρ τ} ⊆
      {sample | ¬BernoulliRowDegreeLowerBound (9 * (d : ℝ) / 10) sample} ∪
        {sample | ¬BernoulliLLYRowLoad d I k₂ k₃ sample} := by
    intro sample hFail
    by_cases hDegree : BernoulliRowDegreeLowerBound (9 * (d : ℝ) / 10) sample
    · right
      intro hLoad
      obtain ⟨x, hUnit, hAlmost, hGradual, hSmall⟩ := hFail
      have hLower := bernoulli_lly_gradual_almost_retained_norm_of_prefix hn hd hk₁ hk₂ hk₃
        hk₁n hk₂n hk₃n hk₂₃ hFit hHalf hPrefix hScale₂ hScale₃ hDensity hRadius I hRows
        sample hDegree hLoad ζ hShift x hUnit hGradual hAlmost
      exact not_lt_of_ge (hLower.trans hSmall) hThreshold
    · exact Or.inl hDegree
  apply (measureReal_mono hSubset (h₂ := by finiteness)).trans
  apply (measureReal_union_le _ _).trans
  exact add_le_add (sparse_bernoulli_row_degree_lower_failure hn hdn)
    (bernoulli_lly_row_load_failure_absorbed hn hd hdn hk₂ hk₃ ha haOne hRank₂ hRank₃
      I hRows hEntropy0 hEntropy hDimension)

end CircularLaw
