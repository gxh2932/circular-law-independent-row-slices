import CircularLaw.GaussianFirstPairAssembly

/-!
# Noncrossing is preserved by first-pair assembly

An interior edge sees the initial endpoint below both ends and the first
partner above both ends. Final-interval edges see both endpoints below
them. Cross-interval pairs therefore stay on one side of every circular
cut, while cuts within one interval are preserved by its increasing map.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem finite_circular_cut_below {n : ℕ} (i j v : Fin n)
    (hi : v < i) (hj : v < j) : finiteCircularCut i j v ↔ i < j := by
  simp only [finiteCircularCut]
  split_ifs <;> omega

theorem finite_circular_cut_above {n : ℕ} (i j v : Fin n)
    (hi : i < v) (hj : j < v) : finiteCircularCut i j v ↔ i < j := by
  simp only [finiteCircularCut]
  split_ifs <;> omega

theorem gaussian_first_interior_position_bounds {k : ℕ} (q : Fin (k + 1))
    (a : Fin (q.val - 1)) :
    0 < gaussianFirstInteriorMap q a ∧ gaussianFirstInteriorMap q a < q :=
  (gaussian_first_interior_map_range q _).mp ⟨a, rfl⟩

theorem gaussian_first_outer_position_bound {k : ℕ} (q : Fin (k + 1))
    (a : Fin (k - q.val)) : q < gaussianFirstOuterMap q a :=
  (gaussian_first_outer_map_range q _).mp ⟨a, rfl⟩

theorem gaussian_first_interior_not_cut {k : ℕ} (q : Fin (k + 1))
    (a : Fin (q.val - 1)) : ¬ finiteCircularCut 0 q (gaussianFirstInteriorMap q a) := by
  simp only [finiteCircularCut, Fin.lt_def, Fin.le_def, Fin.val_zero, gaussianFirstInteriorMap]
  split_ifs <;> omega

theorem gaussian_first_outer_cut {k : ℕ} (q : Fin (k + 1)) (hq : 0 < q)
    (a : Fin (k - q.val)) : finiteCircularCut 0 q (gaussianFirstOuterMap q a) := by
  simp only [finiteCircularCut, if_pos hq]
  exact Or.inr (gaussian_first_outer_position_bound q a)

theorem gaussian_first_pair_assembly_noncrossing {k : ℕ} (b : Fin (k + 1) → Bool)
    (q : Fin (k + 1)) (hZero : b 0 = false) (hQ : b q = true)
    (eI : GaussianWordPairing (b ∘ gaussianFirstInteriorMap q))
    (eO : GaussianWordPairing (b ∘ gaussianFirstOuterMap q))
    (hI : GaussianWordNoncrossing (b ∘ gaussianFirstInteriorMap q) eI)
    (hO : GaussianWordNoncrossing (b ∘ gaussianFirstOuterMap q) eO) :
    GaussianWordNoncrossing b (gaussianFirstPairAssembly b q hZero hQ eI eO) := by
  have hq : (0 : Fin (k + 1)) < q := by
    have h := gaussian_noncrossing_first_partner_pos k b
      (gaussianFirstPairAssembly b q hZero hQ eI eO) hZero
    simpa only [gaussian_first_pair_assembly_first, Subtype.coe_mk] using h
  intro a c hca
  obtain ⟨a, rfl⟩ := (gaussianFirstFiberEquiv b q hZero hQ false).surjective a
  obtain ⟨c, rfl⟩ := (gaussianFirstFiberEquiv b q hZero hQ false).surjective c
  simp only [gaussian_first_pair_assembly_on_piece]
  rcases a with u | (i | o) <;> rcases c with v | (j | p)
  · exact (hca rfl).elim
  · change finiteCircularCut 0 q (gaussianFirstInteriorMap q j.val) ↔
      finiteCircularCut 0 q (gaussianFirstInteriorMap q (eI j).val)
    exact iff_of_false (gaussian_first_interior_not_cut q j.val)
      (gaussian_first_interior_not_cut q (eI j).val)
  · change finiteCircularCut 0 q (gaussianFirstOuterMap q p.val) ↔
      finiteCircularCut 0 q (gaussianFirstOuterMap q (eO p).val)
    exact iff_of_true (gaussian_first_outer_cut q hq p.val)
      (gaussian_first_outer_cut q hq (eO p).val)
  · change finiteCircularCut (gaussianFirstInteriorMap q i.val)
      (gaussianFirstInteriorMap q (eI i).val) 0 ↔
      finiteCircularCut (gaussianFirstInteriorMap q i.val) (gaussianFirstInteriorMap q (eI i).val) q
    rw [finite_circular_cut_below _ _ _ (gaussian_first_interior_position_bounds q i.val).1
      (gaussian_first_interior_position_bounds q (eI i).val).1,
      finite_circular_cut_above _ _ _ (gaussian_first_interior_position_bounds q i.val).2
      (gaussian_first_interior_position_bounds q (eI i).val).2]
  · change finiteCircularCut (gaussianFirstInteriorMap q i.val)
      (gaussianFirstInteriorMap q (eI i).val) (gaussianFirstInteriorMap q j.val) ↔
      finiteCircularCut (gaussianFirstInteriorMap q i.val) (gaussianFirstInteriorMap q (eI i).val)
        (gaussianFirstInteriorMap q (eI j).val)
    have hji : j ≠ i := by intro h; subst j; exact hca rfl
    simpa only [finite_circular_cut_strictMono_image _ (gaussian_first_interior_map_strictMono q)]
      using hI i j hji
  · change finiteCircularCut (gaussianFirstInteriorMap q i.val)
      (gaussianFirstInteriorMap q (eI i).val) (gaussianFirstOuterMap q p.val) ↔
      finiteCircularCut (gaussianFirstInteriorMap q i.val) (gaussianFirstInteriorMap q (eI i).val)
        (gaussianFirstOuterMap q (eO p).val)
    rw [finite_circular_cut_above _ _ _
      ((gaussian_first_interior_position_bounds q i.val).2.trans (gaussian_first_outer_position_bound q p.val))
      ((gaussian_first_interior_position_bounds q (eI i).val).2.trans (gaussian_first_outer_position_bound q p.val)),
      finite_circular_cut_above _ _ _
      ((gaussian_first_interior_position_bounds q i.val).2.trans (gaussian_first_outer_position_bound q (eO p).val))
      ((gaussian_first_interior_position_bounds q (eI i).val).2.trans (gaussian_first_outer_position_bound q (eO p).val))]
  · change finiteCircularCut (gaussianFirstOuterMap q o.val)
      (gaussianFirstOuterMap q (eO o).val) 0 ↔
      finiteCircularCut (gaussianFirstOuterMap q o.val) (gaussianFirstOuterMap q (eO o).val) q
    rw [finite_circular_cut_below _ _ _ (hq.trans (gaussian_first_outer_position_bound q o.val))
      (hq.trans (gaussian_first_outer_position_bound q (eO o).val)),
      finite_circular_cut_below _ _ _ (gaussian_first_outer_position_bound q o.val)
      (gaussian_first_outer_position_bound q (eO o).val)]
  · change finiteCircularCut (gaussianFirstOuterMap q o.val)
      (gaussianFirstOuterMap q (eO o).val) (gaussianFirstInteriorMap q j.val) ↔
      finiteCircularCut (gaussianFirstOuterMap q o.val) (gaussianFirstOuterMap q (eO o).val)
        (gaussianFirstInteriorMap q (eI j).val)
    rw [finite_circular_cut_below _ _ _
      ((gaussian_first_interior_position_bounds q j.val).2.trans (gaussian_first_outer_position_bound q o.val))
      ((gaussian_first_interior_position_bounds q j.val).2.trans (gaussian_first_outer_position_bound q (eO o).val)),
      finite_circular_cut_below _ _ _
      ((gaussian_first_interior_position_bounds q (eI j).val).2.trans (gaussian_first_outer_position_bound q o.val))
      ((gaussian_first_interior_position_bounds q (eI j).val).2.trans (gaussian_first_outer_position_bound q (eO o).val))]
  · change finiteCircularCut (gaussianFirstOuterMap q o.val)
      (gaussianFirstOuterMap q (eO o).val) (gaussianFirstOuterMap q p.val) ↔
      finiteCircularCut (gaussianFirstOuterMap q o.val) (gaussianFirstOuterMap q (eO o).val)
        (gaussianFirstOuterMap q (eO p).val)
    have hpo : p ≠ o := by intro h; subst p; exact hca rfl
    simpa only [finite_circular_cut_strictMono_image _ (gaussian_first_outer_map_strictMono q)]
      using hO o p hpo

end CircularLaw
