import CircularLaw.GaussianWordNoncrossingCounts

/-!
# A noncrossing pair splits the actual compatible matching

Every matched pair is wholly inside or wholly outside the strict interval
between the endpoints of another pair. At first position zero the outer
piece is the ordinary final interval. Both restricted bijections retain
the actual direct and adjoint positions, so their counts agree exactly.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem gaussian_direct_adjoint_positions_ne {α : Type*} (b : α → Bool)
    (c : GaussianDirectPositions b) (d : GaussianAdjointPositions b) : c.val ≠ d.val := by
  intro h
  have hBool := congrArg b h
  rw [c.property, d.property] at hBool
  exact Bool.noConfusion hBool

theorem gaussian_noncrossing_pair_interior_iff (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e)
    (a c : GaussianDirectPositions b) :
    (min a.val (e a).val < c.val ∧ c.val < max a.val (e a).val) ↔
      (min a.val (e a).val < (e c).val ∧ (e c).val < max a.val (e a).val) := by
  by_cases hca : c = a
  · subst c
    simp only [min_def, max_def]
    split_ifs <;> omega
  · have hcpa : c.val ≠ a.val := fun h => hca (Subtype.ext h)
    have hcqa := gaussian_direct_adjoint_positions_ne b c (e a)
    have hqcpa := (gaussian_direct_adjoint_positions_ne b a (e c)).symm
    have hqcqa : (e c).val ≠ (e a).val := fun h => hca (e.injective (Subtype.ext h))
    have hCut := hNC a c hca
    simp only [finiteCircularCut, min_def, max_def] at hCut ⊢
    split_ifs at hCut ⊢ <;> omega

def gaussianNoncrossingInteriorPairing (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e)
    (a : GaussianDirectPositions b) :
    {c : GaussianDirectPositions b // min a.val (e a).val < c.val ∧ c.val < max a.val (e a).val} ≃
      {d : GaussianAdjointPositions b // min a.val (e a).val < d.val ∧ d.val < max a.val (e a).val} :=
  e.subtypeEquiv (gaussian_noncrossing_pair_interior_iff k b e hNC a)

theorem gaussian_noncrossing_interior_counts_equal (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e)
    (a : GaussianDirectPositions b) :
    Fintype.card {c : GaussianDirectPositions b //
      min a.val (e a).val < c.val ∧ c.val < max a.val (e a).val} =
      Fintype.card {d : GaussianAdjointPositions b //
        min a.val (e a).val < d.val ∧ d.val < max a.val (e a).val} :=
  Fintype.card_congr (gaussianNoncrossingInteriorPairing k b e hNC a)

theorem gaussian_noncrossing_first_partner_pos (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hZero : b 0 = false) :
    0 < (e ⟨0, hZero⟩).val := by
  have hNe := gaussian_direct_adjoint_positions_ne b ⟨0, hZero⟩ (e ⟨0, hZero⟩)
  change (0 : Fin (k + 1)) ≠ (e ⟨0, hZero⟩).val at hNe
  simp only [ne_eq, Fin.ext_iff, Fin.val_zero] at hNe
  simp only [Fin.lt_def, Fin.val_zero]
  omega

theorem gaussian_noncrossing_first_outer_iff (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e)
    (hZero : b 0 = false) (c : GaussianDirectPositions b) :
    (e ⟨0, hZero⟩).val < c.val ↔ (e ⟨0, hZero⟩).val < (e c).val := by
  by_cases hca : c = ⟨0, hZero⟩
  · subst c
    change (e ⟨0, hZero⟩).val < 0 ↔ (e ⟨0, hZero⟩).val < (e ⟨0, hZero⟩).val
    exact iff_of_false (not_lt_of_ge (Fin.zero_le _)) (lt_irrefl _)
  · have hcNe : c.val ≠ 0 := fun h => hca (Subtype.ext h)
    have hqcNe := (gaussian_direct_adjoint_positions_ne b ⟨0, hZero⟩ (e c)).symm
    have hcPos : (0 : Fin (k + 1)) < c.val := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_zero] at hcNe
      simp only [Fin.lt_def, Fin.val_zero]
      omega
    have hqcPos : (0 : Fin (k + 1)) < (e c).val := by
      change (e c).val ≠ (0 : Fin (k + 1)) at hqcNe
      simp only [ne_eq, Fin.ext_iff, Fin.val_zero] at hqcNe
      simp only [Fin.lt_def, Fin.val_zero]
      omega
    have hQ := gaussian_noncrossing_first_partner_pos k b e hZero
    have hCut := hNC ⟨0, hZero⟩ c hca
    simpa only [Subtype.coe_mk, finiteCircularCut, if_pos hQ, not_le_of_gt hcPos, not_le_of_gt hqcPos,
      false_or] using hCut

def gaussianNoncrossingFirstOuterPairing (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false) :
    {c : GaussianDirectPositions b // (e ⟨0, hZero⟩).val < c.val} ≃
      {d : GaussianAdjointPositions b // (e ⟨0, hZero⟩).val < d.val} :=
  e.subtypeEquiv (gaussian_noncrossing_first_outer_iff k b e hNC hZero)

theorem gaussian_noncrossing_first_outer_counts_equal (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) (hZero : b 0 = false) :
    Fintype.card {c : GaussianDirectPositions b // (e ⟨0, hZero⟩).val < c.val} =
      Fintype.card {d : GaussianAdjointPositions b // (e ⟨0, hZero⟩).val < d.val} :=
  Fintype.card_congr (gaussianNoncrossingFirstOuterPairing k b e hNC hZero)

end CircularLaw
