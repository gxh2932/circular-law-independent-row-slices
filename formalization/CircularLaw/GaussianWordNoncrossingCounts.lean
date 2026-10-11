import CircularLaw.GaussianWordTreeCuts
import CircularLaw.FiniteLabeledSeparators
import CircularLaw.GaussianShiftedMomentMeanLimits
import CircularLaw.GaussianShiftedWeakLimit

/-!
# Exact limiting word means count noncrossing compatible pairings

Noncrossing circular cuts respect every reversed endpoint identification
and descend to the actual vertex quotient. Each descended cut separates
its own edge and is constant across the others. The separator theorem
therefore forces the maximal vertex count. Together with the tree-cut
argument this proves both directions and the exact counting formula.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped Topology

namespace CircularLaw

theorem gaussian_word_noncrossing_cut_coloring (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e)
    (a c : GaussianDirectPositions b) :
    (finiteCircularCut a.val (e a).val c.val ↔
      finiteCircularCut a.val (e a).val (finRotate (k + 1) (e c).val)) ∧
    (finiteCircularCut a.val (e a).val (finRotate (k + 1) c.val) ↔
      finiteCircularCut a.val (e a).val (e c).val) := by
  by_cases hca : c = a
  · subst c
    exact ⟨iff_of_true (finite_circular_cut_start _ _ (gaussian_word_pairing_positions_distinct b e a))
      (finite_circular_cut_after_end _ _ (gaussian_word_pairing_positions_distinct b e a)),
      iff_of_false (finite_circular_cut_after_start _ _) (finite_circular_cut_not_end _ _)⟩
  · have hDirect : c.val ≠ a.val := fun h => hca (Subtype.ext h)
    have hAdjoint : (e c).val ≠ (e a).val := fun h => hca (e.injective (Subtype.ext h))
    have hCrossDirect : c.val ≠ (e a).val := by
      intro h
      have hBool := congrArg b h
      rw [c.property, (e a).property] at hBool
      exact Bool.noConfusion hBool
    have hCrossAdjoint : (e c).val ≠ a.val := by
      intro h
      have hBool := congrArg b h
      rw [(e c).property, a.property] at hBool
      exact Bool.noConfusion hBool
    exact ⟨(hNC a c hca).trans
      (finite_circular_cut_other_successor a.val (e a).val (e c).val hCrossAdjoint hAdjoint).symm,
      (finite_circular_cut_other_successor a.val (e a).val c.val hDirect hCrossDirect).trans
        (hNC a c hca)⟩

theorem gaussian_word_noncrossing_cut_relation (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e)
    (a : GaussianDirectPositions b) :
    ∀ v w, pairedWalkRelation (finRotate (k + 1))
      (fun c : GaussianDirectPositions b => c.val) (fun c => (e c).val) v w →
      finiteCircularCut a.val (e a).val v = finiteCircularCut a.val (e a).val w := by
  apply (paired_walk_coloring_iff _ _ _ _).mpr
  intro c
  have h := gaussian_word_noncrossing_cut_coloring k b e hNC a c
  exact ⟨propext h.1, propext h.2⟩

def gaussianNoncrossingVertexCut (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e)
    (a : GaussianDirectPositions b) : GaussianWordVertexClass b (finRotate (k + 1)) e → Prop :=
  Quotient.lift (finiteCircularCut a.val (e a).val) (fun _ _ h =>
    relation_coloring_eqv_gen _ _ (gaussian_word_noncrossing_cut_relation k b e hNC a) h)

theorem gaussian_noncrossing_vertex_cut_apply (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e)
    (a : GaussianDirectPositions b) (v : Fin (k + 1)) :
    gaussianNoncrossingVertexCut k b e hNC a (gaussianWordVertex b (finRotate (k + 1)) e v) ↔
      finiteCircularCut a.val (e a).val v := Iff.rfl

theorem gaussian_word_noncrossing_leading (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) (hNC : GaussianWordNoncrossing b e) :
    gaussianWordVertexExponent b (finRotate (k + 1)) e =
      Fintype.card (GaussianDirectPositions b) + 1 := by
  apply finite_labeled_separator_vertex_card
    (fun a : GaussianDirectPositions b => gaussianWordVertex b (finRotate (k + 1)) e a.val)
    (fun a => gaussianWordVertex b (finRotate (k + 1)) e (finRotate (k + 1) a.val))
    (gaussianNoncrossingVertexCut k b e hNC)
  · intro a
    exact finite_circular_cut_start _ _ (gaussian_word_pairing_positions_distinct b e a)
  · intro a
    exact finite_circular_cut_after_start _ _
  · intro a c hca
    exact (hNC a c hca).trans (gaussian_word_noncrossing_cut_coloring k b e hNC a c).2.symm
  · exact gaussian_word_pairing_graph_connected b _ e (fin_rotate_same_cycle k)

theorem gaussian_word_leading_iff_noncrossing (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) :
    gaussianWordVertexExponent b (finRotate (k + 1)) e =
      Fintype.card (GaussianDirectPositions b) + 1 ↔ GaussianWordNoncrossing b e :=
  ⟨gaussian_word_leading_noncrossing k b e, gaussian_word_noncrossing_leading k b e⟩

theorem gaussian_word_leading_count_eq_noncrossing_card (k : ℕ) (b : Fin (k + 1) → Bool) :
    gaussianWordLeadingCount k b = Fintype.card {e : GaussianWordPairing b // GaussianWordNoncrossing b e} :=
  Fintype.card_congr (Equiv.subtypeEquivRight (gaussian_word_leading_iff_noncrossing k b))

theorem gaussian_word_mean_count_eq_noncrossing_card (k : ℕ) (b : Fin (k + 1) → Bool) :
    gaussianWordMeanCount (List.ofFn b) =
      Fintype.card {e : GaussianWordPairing b // GaussianWordNoncrossing b e} := by
  by_cases h : Nonempty (GaussianWordPairing b)
  · obtain ⟨e₀⟩ := h
    rw [gaussian_word_mean_count_balanced k b e₀]
    exact gaussian_word_leading_count_eq_noncrossing_card k b
  · letI : IsEmpty (GaussianWordPairing b) := ⟨fun e => h ⟨e⟩⟩
    have hCount : (List.ofFn b).count false ≠ (List.ofFn b).count true := by
      intro hCount
      have hCard : Fintype.card (GaussianDirectPositions b) =
          Fintype.card (GaussianAdjointPositions b) := by
        simpa only [list_ofFn_count_eq_fiber_card] using hCount
      exact h ⟨Fintype.equivOfCardEq hCard⟩
    rw [gaussian_word_mean_count_unbalanced _ hCount]
    exact (Fintype.card_eq_zero).symm

def gaussianNoncrossingWordCount : List Bool → ℕ
  | [] => 1
  | b :: w => Fintype.card {e : GaussianWordPairing (b :: w).get //
      GaussianWordNoncrossing (b :: w).get e}

theorem gaussian_word_mean_count_eq_noncrossing_word_count (w : List Bool) :
    gaussianWordMeanCount w = gaussianNoncrossingWordCount w := by
  cases w with
  | nil => exact gaussian_word_mean_count_nil
  | cons b w =>
    simpa only [List.ofFn_get, gaussianNoncrossingWordCount] using
      gaussian_word_mean_count_eq_noncrossing_card w.length (b :: w).get

theorem gaussian_shifted_moment_limit_eq_noncrossing_sum (z : ℂ) (k : ℕ) :
    gaussianShiftedMomentMeanLimit z k =
      ((scalarShiftWordExpansion z (gramMatrixWord k)).map
        (fun p => p.1 * (gaussianNoncrossingWordCount p.2 : ℂ))).sum := by
  simp only [gaussianShiftedMomentMeanLimit, gaussian_word_mean_count_eq_noncrossing_word_count]

theorem gaussian_normalized_word_mean_tendsto_noncrossing (w : List Bool) :
    Tendsto (fun n : ℕ => gaussianNormalizedWordComplexMean n w) atTop
      (𝓝 (gaussianNoncrossingWordCount w : ℂ)) := by
  simpa only [gaussian_word_mean_count_eq_noncrossing_word_count] using
    gaussian_word_mean_count_tendsto w

theorem gaussian_shifted_limit_even_moments_eq_noncrossing_sum (z : ℂ) (k : ℕ) :
    (∫ t, (t : ℝ) ^ (2 * k) ∂gaussianShiftedSingularLimit z) =
      (((scalarShiftWordExpansion z (gramMatrixWord k)).map
        (fun p => p.1 * (gaussianNoncrossingWordCount p.2 : ℂ))).sum).re := by
  rw [gaussian_shifted_limit_even_moments, gaussianShiftedSquaredMomentLimit,
    gaussian_shifted_moment_limit_eq_noncrossing_sum]

theorem gaussian_shifted_moments_converge_to_noncrossing_sum (z : ℂ) (k : ℕ) :
    VaryingConvergesInProbability gaussianSquareMatrixLaw
      (fun _ => gaussianShiftedSingularMoment z k)
      (((scalarShiftWordExpansion z (gramMatrixWord k)).map
        (fun p => p.1 * (gaussianNoncrossingWordCount p.2 : ℂ))).sum).re := by
  have h := gaussian_shifted_singular_moment_converges_in_probability z k
  rw [gaussian_shifted_moment_limit_eq_noncrossing_sum] at h
  exact h

end CircularLaw
