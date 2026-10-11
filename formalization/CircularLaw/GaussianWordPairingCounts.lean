import CircularLaw.GaussianBijectionPairings
import CircularLaw.PairedClosedWalk
import CircularLaw.GaussianMatrixWords
import CircularLaw.MatrixWordWalks

/-!
# Exact vertex-count formula for arbitrary balanced Gaussian words

The direct and adjoint positions are matched by all bijections. Every
matching identifies the endpoints of its reversed adjoint edges. Its
contribution is exactly the dimension to the number of quotient vertex
classes. For a single closed walk that exponent is at most the number
of direct factors plus one, irrespective of their order.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators Matrix

namespace CircularLaw

abbrev GaussianDirectPositions {α : Type*} (b : α → Bool) := {a // b a = false}

abbrev GaussianAdjointPositions {α : Type*} (b : α → Bool) := {a // b a = true}

abbrev GaussianWordPairing {α : Type*} (b : α → Bool) :=
  GaussianDirectPositions b ≃ GaussianAdjointPositions b

theorem finite_bool_product_split {α M : Type*} [Fintype α] [DecidableEq α] [CommMonoid M]
    (b : α → Bool) (f g : α → M) :
    (∏ a, if b a then g a else f a) =
      (∏ a : GaussianDirectPositions b, f a) *
        ∏ a : GaussianAdjointPositions b, g a := by
  let e : {a // ¬b a = false} ≃ GaussianAdjointPositions b :=
    Equiv.subtypeEquivRight (fun a => by cases b a <;> simp)
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun a => b a = false)]
  congr 1
  · apply Finset.prod_congr rfl
    intro a _
    simp only [a.property, Bool.false_eq_true, if_false]
  · rw [← e.prod_comp (fun a => g a.val)]
    apply Finset.prod_congr rfl
    intro a _
    have h : b a = true := by simpa using a.property
    simp only [h, if_true]
    rfl

def gaussianWordVertexExponent {α : Type*} [Fintype α] [DecidableEq α] (b : α → Bool)
    (ρ : Equiv.Perm α) (e : GaussianWordPairing b) : ℕ :=
  relationClassCount (pairedWalkRelation ρ
    (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val))

theorem gaussian_word_pairing_covers_positions {α : Type*} (b : α → Bool)
    (e : GaussianWordPairing b) (v : α) :
    (∃ a : GaussianDirectPositions b, a.val = v) ∨
      ∃ a : GaussianDirectPositions b, (e a).val = v := by
  cases h : b v with
  | false => exact Or.inl ⟨⟨v, h⟩, rfl⟩
  | true =>
    refine Or.inr ⟨e.symm ⟨v, h⟩, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨v, h⟩)

theorem gaussian_word_vertex_exponent_bound {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b)
    (hOrbit : ∀ v w, ρ.SameCycle v w) :
    gaussianWordVertexExponent b ρ e ≤ Fintype.card (GaussianDirectPositions b) + 1 := by
  exact paired_walk_class_count_bound ρ _ _ (gaussian_word_pairing_covers_positions b e) hOrbit

theorem gaussian_word_pairing_assignment_count {α : Type*} [Fintype α] [DecidableEq α]
    (b : α → Bool) (ρ : Equiv.Perm α) (e : GaussianWordPairing b) (n : ℕ) :
    (∑ v : α → Fin n, if ∀ a : GaussianDirectPositions b,
      v a = v (ρ (e a)) ∧ v (ρ a) = v (e a) then (1 : ℂ) else 0) =
      (n : ℂ) ^ gaussianWordVertexExponent b ρ e := by
  rw [finite_complex_indicator_sum]
  have h := paired_walk_coloring_card ρ
    (fun a : GaussianDirectPositions b => a.val) (fun a => (e a).val) n
  simp only [Fintype.card_subtype] at h ⊢
  exact_mod_cast h

def gaussianWordClosedWalk {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (b : α → Bool) (ρ : Equiv.Perm α) (v : α → Fin n) (x : GaussianSquareSample n) : ℂ :=
  ∏ t, if b t then star (x (v (ρ t), v t)) else x (v t, v (ρ t))

theorem gaussian_word_closed_walk_split {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (b : α → Bool) (ρ : Equiv.Perm α) (v : α → Fin n) (x : GaussianSquareSample n) :
    gaussianWordClosedWalk b ρ v x =
      (∏ a : GaussianDirectPositions b, x (v a, v (ρ a))) *
        ∏ a : GaussianAdjointPositions b, star (x (v (ρ a), v a)) :=
  finite_bool_product_split b _ _

theorem gaussian_word_closed_walk_integrable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (b : α → Bool) (ρ : Equiv.Perm α) (v : α → Fin n) (e₀ : GaussianWordPairing b) :
    Integrable (gaussianWordClosedWalk b ρ v) (gaussianSquareMatrixLaw n) := by
  change Integrable (fun x => gaussianWordClosedWalk b ρ v x) _
  simp only [gaussian_word_closed_walk_split]
  exact gaussian_entry_bijection_integrable e₀ _ _

theorem gaussian_word_closed_walk_integral {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (b : α → Bool) (ρ : Equiv.Perm α) (v : α → Fin n) (e₀ : GaussianWordPairing b) :
    (∫ x, gaussianWordClosedWalk b ρ v x ∂gaussianSquareMatrixLaw n) =
      ∑ e : GaussianWordPairing b,
        if ∀ a : GaussianDirectPositions b,
          v a = v (ρ (e a)) ∧ v (ρ a) = v (e a) then (1 : ℂ) else 0 := by
  simp only [gaussian_word_closed_walk_split]
  rw [gaussianSquareMatrixLaw, gaussian_entry_bijection_wick e₀]
  simp only [Prod.mk.injEq, finite_complex_indicator_product]
  apply Finset.sum_congr (by ext e; simp only [Finset.mem_univ])
  intro e _
  split_ifs <;> rfl

theorem gaussian_word_walk_sum_integral {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (b : α → Bool) (ρ : Equiv.Perm α) (e₀ : GaussianWordPairing b) :
    (∫ x, (∑ v : α → Fin n, gaussianWordClosedWalk b ρ v x) ∂gaussianSquareMatrixLaw n) =
      ∑ e : GaussianWordPairing b, (n : ℂ) ^ gaussianWordVertexExponent b ρ e := by
  rw [integral_finset_sum _ (fun v _ => gaussian_word_closed_walk_integrable b ρ v e₀)]
  simp only [gaussian_word_closed_walk_integral b ρ _ e₀]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun e _ => gaussian_word_pairing_assignment_count b ρ e n)

theorem gaussian_matrix_word_closed_walk_sum {n : ℕ} (k : ℕ)
    (b : Fin (k + 1) → Bool) (x : GaussianSquareSample n) :
    (gaussianMatrixWord (List.ofFn b) x).trace =
      ∑ v : Fin (k + 1) → Fin n, gaussianWordClosedWalk b (finRotate (k + 1)) v x := by
  rw [gaussianMatrixWord, List.map_ofFn, matrix_word_trace_closed_walk_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.prod_congr rfl
  intro t _
  cases h : b t <;> simp only [Function.comp_apply, h, Bool.false_eq_true, if_false, if_true,
    Matrix.conjTranspose_apply, gaussianSquareMatrix]

theorem gaussian_matrix_word_vertex_integral (n k : ℕ) (b : Fin (k + 1) → Bool)
    (e₀ : GaussianWordPairing b) :
    (∫ x, (gaussianMatrixWord (List.ofFn b) x).trace ∂gaussianSquareMatrixLaw n) =
      ∑ e : GaussianWordPairing b,
        (n : ℂ) ^ gaussianWordVertexExponent b (finRotate (k + 1)) e := by
  simp only [gaussian_matrix_word_closed_walk_sum]
  exact gaussian_word_walk_sum_integral b (finRotate (k + 1)) e₀

theorem gaussian_matrix_word_vertex_exponent_bound (k : ℕ) (b : Fin (k + 1) → Bool)
    (e : GaussianWordPairing b) :
    gaussianWordVertexExponent b (finRotate (k + 1)) e ≤
      Fintype.card (GaussianDirectPositions b) + 1 :=
  gaussian_word_vertex_exponent_bound b _ e (fin_rotate_same_cycle k)

end CircularLaw
