import CircularLaw.GaussianWordDerivative

/-!
# Linear evaluation of finite scalar-shift expansions

These finite list identities expand the deletion derivative of a shifted
word into the shifted prefix and shifted suffix at every opposite symbol.
They hold for an arbitrary complex-valued evaluation of word pairs.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def scalarShiftWordEvaluate (z : ℂ) (w : List Bool) (f : List Bool → ℂ) : ℂ :=
  ((scalarShiftWordExpansion z w).map (fun p => p.1 * f p.2)).sum

def scalarShiftPairEvaluate (z : ℂ) (u v : List Bool)
    (f : List Bool × List Bool → ℂ) : ℂ :=
  scalarShiftWordEvaluate z u (fun l => scalarShiftWordEvaluate z v (fun r => f (l, r)))

def scalarShiftWordDerivativeEvaluate (z : ℂ) (b : Bool) (w : List Bool)
    (f : List Bool × List Bool → ℂ) : ℂ :=
  scalarShiftWordEvaluate z w (fun u => ((gaussianWordDerivative b u).map f).sum)

theorem scalar_shift_word_evaluate_nil (z : ℂ) (f : List Bool → ℂ) :
    scalarShiftWordEvaluate z [] f = f [] := by
  simp [scalarShiftWordEvaluate, scalarShiftWordExpansion]

theorem scalar_shift_word_evaluate_zero (z : ℂ) (w : List Bool) :
    scalarShiftWordEvaluate z w (fun _ => 0) = 0 := by
  simp [scalarShiftWordEvaluate]

theorem scalar_shift_word_evaluate_add (z : ℂ) (w : List Bool) (f g : List Bool → ℂ) :
    scalarShiftWordEvaluate z w (fun u => f u + g u) =
      scalarShiftWordEvaluate z w f + scalarShiftWordEvaluate z w g := by
  simp only [scalarShiftWordEvaluate, mul_add, List.sum_map_add]

theorem scalar_shift_word_evaluate_mul (z : ℂ) (w : List Bool)
    (a : ℂ) (f : List Bool → ℂ) :
    scalarShiftWordEvaluate z w (fun u => a * f u) = a * scalarShiftWordEvaluate z w f := by
  simp only [scalarShiftWordEvaluate, mul_left_comm]
  rw [List.sum_map_mul_left]

theorem scalar_shift_word_evaluate_cons (z : ℂ) (b : Bool) (w : List Bool)
    (f : List Bool → ℂ) :
    scalarShiftWordEvaluate z (b :: w) f =
      scalarShiftWordEvaluate z w (fun u => f (b :: u)) +
        scalarShiftWordFactor z b * scalarShiftWordEvaluate z w f := by
  simp only [scalarShiftWordEvaluate, scalarShiftWordExpansion, List.map_append,
    List.sum_append, List.map_map, Function.comp_def, mul_assoc]
  rw [List.sum_map_mul_left]

theorem scalar_shift_word_factor_real (r : ℝ) (b : Bool) :
    scalarShiftWordFactor (r : ℂ) b = -(r : ℂ) := by
  cases b <;> simp [scalarShiftWordFactor]

theorem scalar_shift_word_evaluate_map_not_real (r : ℝ) (w : List Bool)
    (f : List Bool → ℂ) :
    scalarShiftWordEvaluate (r : ℂ) (w.map Bool.not) f =
      scalarShiftWordEvaluate (r : ℂ) w (fun u => f (u.map Bool.not)) := by
  induction w generalizing f with
  | nil => simp [scalar_shift_word_evaluate_nil]
  | cons b w ih =>
    simp only [List.map_cons, scalar_shift_word_evaluate_cons, scalar_shift_word_factor_real]
    rw [ih, ih]

theorem scalar_shift_pair_evaluate_nil_left (z : ℂ) (v : List Bool)
    (f : List Bool × List Bool → ℂ) :
    scalarShiftPairEvaluate z [] v f = scalarShiftWordEvaluate z v (fun r => f ([], r)) := by
  exact scalar_shift_word_evaluate_nil z _

theorem scalar_shift_pair_evaluate_cons_left (z : ℂ) (b : Bool) (u v : List Bool)
    (f : List Bool × List Bool → ℂ) :
    scalarShiftPairEvaluate z (b :: u) v f = scalarShiftPairEvaluate z u v
      (fun p => f (b :: p.1, p.2) + scalarShiftWordFactor z b * f p) := by
  simp only [scalarShiftPairEvaluate, scalar_shift_word_evaluate_cons,
    scalar_shift_word_evaluate_add, scalar_shift_word_evaluate_mul]

theorem gaussian_word_derivative_cons_evaluate (b c : Bool) (w : List Bool)
    (f : List Bool × List Bool → ℂ) :
    ((gaussianWordDerivative b (c :: w)).map f).sum =
      (if c ≠ b then f ([], w) else 0) +
        ((gaussianWordDerivative b w).map (fun p => f (c :: p.1, p.2))).sum := by
  by_cases h : c ≠ b <;>
    simp [gaussianWordDerivative, h, List.map_map, Function.comp_def]

theorem scalar_shift_word_derivative_evaluate_linear (z : ℂ) (b : Bool) (w : List Bool)
    (a : ℂ) (f g : List Bool × List Bool → ℂ) :
    scalarShiftWordDerivativeEvaluate z b w (fun p => f p + a * g p) =
      scalarShiftWordDerivativeEvaluate z b w f + a * scalarShiftWordDerivativeEvaluate z b w g := by
  simp only [scalarShiftWordDerivativeEvaluate, List.sum_map_add, List.sum_map_mul_left,
    scalar_shift_word_evaluate_add, scalar_shift_word_evaluate_mul]

theorem scalar_shift_word_derivative_evaluate_cons (z : ℂ) (b c : Bool) (w : List Bool)
    (f : List Bool × List Bool → ℂ) :
    scalarShiftWordDerivativeEvaluate z b (c :: w) f =
      (if c ≠ b then scalarShiftWordEvaluate z w (fun u => f ([], u)) else 0) +
        scalarShiftWordDerivativeEvaluate z b w
          (fun p => f (c :: p.1, p.2) + scalarShiftWordFactor z c * f p) := by
  simp only [scalarShiftWordDerivativeEvaluate, scalar_shift_word_evaluate_cons,
    gaussian_word_derivative_cons_evaluate, List.sum_map_add, List.sum_map_mul_left,
    scalar_shift_word_evaluate_add, scalar_shift_word_evaluate_mul]
  by_cases h : c ≠ b <;>
    simp [h, scalar_shift_word_evaluate_zero, add_assoc]

theorem scalar_shift_word_derivative_evaluate_sum (z : ℂ) (b : Bool) (w : List Bool)
    (f : List Bool × List Bool → ℂ) :
    scalarShiftWordDerivativeEvaluate z b w f =
      ∑ q : Fin w.length, if w.get q ≠ b then
        scalarShiftPairEvaluate z (w.take q.val) (w.drop (q.val + 1)) f else 0 := by
  induction w generalizing f with
  | nil => simp [scalarShiftWordDerivativeEvaluate, scalar_shift_word_evaluate_nil,
      gaussianWordDerivative]
  | cons c w ih =>
    rw [scalar_shift_word_derivative_evaluate_cons, ih]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, List.take_zero,
      zero_add, List.drop_succ_cons, List.drop_zero, scalar_shift_pair_evaluate_nil_left]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    simp only [Fin.val_succ, List.getElem_cons_succ, List.take_succ_cons,
      scalar_shift_pair_evaluate_cons_left]

theorem scalar_shift_pair_evaluate_product (z : ℂ) (u v : List Bool)
    (f g : List Bool → ℂ) :
    scalarShiftPairEvaluate z u v (fun p => f p.1 * g p.2) =
      scalarShiftWordEvaluate z u f * scalarShiftWordEvaluate z v g := by
  unfold scalarShiftPairEvaluate
  simp only [scalar_shift_word_evaluate_mul]
  unfold scalarShiftWordEvaluate
  simp only [← mul_assoc]
  rw [List.sum_map_mul_right]

end CircularLaw
