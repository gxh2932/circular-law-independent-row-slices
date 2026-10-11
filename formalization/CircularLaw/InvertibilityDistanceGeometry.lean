import CircularLaw.FiniteRowDistanceDual

/-!
# Invertibility via actual leave-one-out row distances

This is the geometric input of LLY26a Lemma 7.1. The source infimum is
an extended nonnegative infimum over its actual unit non-almost-constant
vectors, so an empty admissible set has value infinity. Finitely many
good distances supply one common lower bound before taking this infimum.
-/

noncomputable section
set_option maxHeartbeats 200000
open Classical
open scoped BigOperators InnerProductSpace ENNReal

namespace CircularLaw

def finiteRowCombination {n : ℕ} (rows : Fin n → EuclideanSpace ℂ (Fin n))
    (c : Fin n → ℂ) : EuclideanSpace ℂ (Fin n) := ∑ i, c i • rows i

def sourceNonAlmostConstant {n : ℕ} (δ ρ : ℝ) (x : EuclideanSpace ℂ (Fin n)) : Prop :=
  ∀ center : ℂ, ((Finset.univ.filter (fun i => ‖x i - center‖ ≤ ρ / Real.sqrt n)).card : ℝ) ≤ (1 - δ) * n

def sourceNonAlmostRowMinimum {n : ℕ} (rows : Fin n → EuclideanSpace ℂ (Fin n))
    (δ ρ : ℝ) : ℝ≥0∞ :=
  ⨅ x : {x : EuclideanSpace ℂ (Fin n) // ‖x‖ = 1 ∧ sourceNonAlmostConstant δ ρ x},
    ENNReal.ofReal ‖finiteRowCombination rows (fun i => x.val i)‖

def sourceCloseRowDistances {n : ℕ} (rows : Fin n → EuclideanSpace ℂ (Fin n))
    (ε : ℝ) : Finset (Fin n) := Finset.univ.filter (fun i => finiteRowDistance rows i ≤ ε)

theorem finite_row_residual_other_zero {n : ℕ}
    (rows : Fin n → EuclideanSpace ℂ (Fin n)) {i j : Fin n} (hji : j ≠ i) :
    (finiteRowSpanExcept rows i)ᗮ.starProjection (rows j) = 0 := by
  have hRow : rows j ∈ finiteRowSpanExcept rows i :=
    Submodule.subset_span ⟨j, by simpa only [Set.mem_diff, Set.mem_univ,
      Set.mem_singleton_iff, true_and] using hji, rfl⟩
  rw [Submodule.starProjection_orthogonal]
  change rows j - (finiteRowSpanExcept rows i).starProjection (rows j) = 0
  rw [Submodule.starProjection_eq_self_iff.mpr hRow, sub_self]

theorem finite_row_combination_residual {n : ℕ}
    (rows : Fin n → EuclideanSpace ℂ (Fin n)) (c : Fin n → ℂ) (i : Fin n) :
    (finiteRowSpanExcept rows i)ᗮ.starProjection (finiteRowCombination rows c) =
      c i • finiteRowResidual rows i := by
  simp only [finiteRowCombination, map_sum, map_smul]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [finite_row_residual_other_zero rows hji, smul_zero]
  · simp

theorem finite_row_coefficient_distance_bound {n : ℕ}
    (rows : Fin n → EuclideanSpace ℂ (Fin n)) (c : Fin n → ℂ) (i : Fin n) :
    ‖c i‖ * finiteRowDistance rows i ≤ ‖finiteRowCombination rows c‖ := by
  have hBound : ‖(finiteRowSpanExcept rows i)ᗮ.starProjection
      (finiteRowCombination rows c)‖ ≤ ‖finiteRowCombination rows c‖ :=
    Submodule.norm_starProjection_apply_le ((finiteRowSpanExcept rows i)ᗮ)
      (finiteRowCombination rows c)
  calc
    _ = ‖(finiteRowSpanExcept rows i)ᗮ.starProjection (finiteRowCombination rows c)‖ := by
      rw [finite_row_combination_residual, norm_smul, finite_row_residual_norm]
    _ ≤ _ := hBound

theorem source_nonalmost_large_coordinate_count {n : ℕ} (δ ρ : ℝ)
    (x : EuclideanSpace ℂ (Fin n)) (hx : sourceNonAlmostConstant δ ρ x) :
    δ * n ≤ ((Finset.univ.filter (fun i => ρ / Real.sqrt n < ‖x i‖)).card : ℝ) := by
  have hClose := hx 0
  simp only [sub_zero] at hClose
  have hCard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => ‖x i‖ ≤ ρ / Real.sqrt n)
  simp only [not_le, Finset.card_univ, Fintype.card_fin] at hCard
  have hCast := congrArg (fun k : ℕ => (k : ℝ)) hCard
  simp only [Nat.cast_add] at hCast
  nlinarith

theorem source_nonalmost_row_minimum_lower_bound {n : ℕ} (hn : 0 < n)
    (rows : Fin n → EuclideanSpace ℂ (Fin n)) {δ ρ ε : ℝ}
    (hδ : δ ≤ 1)
    (hFew : ((sourceCloseRowDistances rows ε).card : ℝ) < δ * n) :
    ∃ q : ℝ, ε < q ∧ ENNReal.ofReal ((ρ / Real.sqrt n) * q) ≤
      sourceNonAlmostRowMinimum rows δ ρ := by
  let good := Finset.univ.filter (fun i => ε < finiteRowDistance rows i)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hGood : good.Nonempty := by
    by_contra hEmpty
    have hAll : sourceCloseRowDistances rows ε = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hi : i ∉ good := fun hMem => hEmpty ⟨i, hMem⟩
      simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hi
    rw [hAll, Finset.card_univ, Fintype.card_fin] at hFew
    have hδn := mul_le_mul_of_nonneg_right hδ hnR.le
    nlinarith
  obtain ⟨j, hj, hMin⟩ := good.exists_min_image (finiteRowDistance rows) hGood
  have hq : ε < finiteRowDistance rows j := (Finset.mem_filter.mp hj).2
  refine ⟨finiteRowDistance rows j, hq, ?_⟩
  apply le_iInf
  intro x
  have hLarge := source_nonalmost_large_coordinate_count δ ρ x.val x.property.2
  let large := Finset.univ.filter (fun i => ρ / Real.sqrt n < ‖x.val i‖)
  have hNotSub : ¬large ⊆ sourceCloseRowDistances rows ε := by
    intro hSub
    have hCard : (large.card : ℝ) ≤ (sourceCloseRowDistances rows ε).card := by
      exact_mod_cast Finset.card_le_card hSub
    exact not_lt_of_ge (hCard.trans' hLarge) hFew
  obtain ⟨i, hiLarge, hiNotClose⟩ := Finset.not_subset.mp hNotSub
  have hiGood : i ∈ good := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [sourceCloseRowDistances, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hiNotClose
  have hiNorm : ρ / Real.sqrt n ≤ ‖x.val i‖ := (Finset.mem_filter.mp hiLarge).2.le
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul hiNorm (hMin i hiGood) (finite_row_distance_nonneg rows j) (norm_nonneg _)).trans
    (finite_row_coefficient_distance_bound rows (fun k => x.val k) i)

theorem source_nonalmost_small_image_forces_close_rows {n : ℕ} (hn : 0 < n)
    (rows : Fin n → EuclideanSpace ℂ (Fin n)) {δ ρ ε : ℝ}
    (hδ : δ ≤ 1) (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hSmall : sourceNonAlmostRowMinimum rows δ ρ ≤ ENNReal.ofReal (ε * ρ / Real.sqrt n)) :
    δ * n ≤ ((sourceCloseRowDistances rows ε).card : ℝ) := by
  by_contra h
  obtain ⟨q, hq, hLower⟩ := source_nonalmost_row_minimum_lower_bound hn rows hδ (lt_of_not_ge h)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : 0 < ρ / Real.sqrt n := div_pos hρ (Real.sqrt_pos.mpr hnR)
  have hStrict : ε * ρ / Real.sqrt n < (ρ / Real.sqrt n) * q := by
    calc
      _ = (ρ / Real.sqrt n) * ε := by ring
      _ < _ := mul_lt_mul_of_pos_left hq ht
  have hENN : ENNReal.ofReal (ε * ρ / Real.sqrt n) < ENNReal.ofReal ((ρ / Real.sqrt n) * q) := by
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hStrict
  exact not_lt_of_ge (hLower.trans hSmall) hENN

end CircularLaw
