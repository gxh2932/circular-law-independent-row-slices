import CircularLaw.EqualBlock
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# The manuscript row span has exactly the shifted right kernel

The span uses conjugated shifted rows, as in the paper's definition of
`E_I`. Its inner product with a vector is the literal retained matrix
action. Orthogonality to the span is equivalent to vanishing of all
these row actions.
-/

noncomputable section
open Classical
open scoped BigOperators InnerProductSpace

namespace CircularLaw

def retainedConjugateRow {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : I) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun j => star ((retainedShiftedMatrix I ζ rows) i j))

def retainedRowSpan {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  Submodule.span ℂ (Set.range (retainedConjugateRow I ζ rows))

theorem retainedConjugateRow_inner {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (i : I) (v : Fin n → ℂ) :
    ⟪retainedConjugateRow I ζ rows i, WithLp.toLp 2 v⟫_ℂ =
      (retainedShiftedMatrix I ζ rows).mulVec v i := by
  rw [PiLp.inner_apply]
  change (∑ j, v j * star (star ((retainedShiftedMatrix I ζ rows) i j))) = _
  simp only [star_star, Matrix.mulVec, dotProduct, mul_comm]

theorem retainedRowSpan_orthogonal_iff_kernel {n d : ℕ} (I : Finset (Fin n)) (ζ : ℂ)
    (rows : RowSliceMatrix n d) (v : Fin n → ℂ) :
    (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n)) ∈ (retainedRowSpan I ζ rows)ᗮ ↔
      (retainedShiftedMatrix I ζ rows).mulVec v = 0 := by
  constructor
  · intro hv
    funext i
    have hRow : retainedConjugateRow I ζ rows i ∈ retainedRowSpan I ζ rows :=
      Submodule.subset_span (Set.mem_range_self i)
    have hInner := Submodule.inner_right_of_mem_orthogonal hRow hv
    exact (retainedConjugateRow_inner I ζ rows i v).symm.trans hInner
  · intro hKernel
    apply (Submodule.mem_orthogonal _ _).mpr
    intro u hu
    change u ∈ Submodule.span ℂ (Set.range (retainedConjugateRow I ζ rows)) at hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨i, rfl⟩ := hu
      rw [retainedConjugateRow_inner, hKernel]
      rfl
    | zero => simp
    | add x y _ _ hx hy => simp only [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => simp only [inner_smul_left, hx, mul_zero]

end CircularLaw
