import CircularLaw.BernoulliQuadraticMoment
import CircularLaw.MeasureModel
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Exact support fibers of the actual Bernoulli cube

Every cube atom has mass `p^d (1-p)^(n-d)` at support size `d`.
The support-size fiber is in bijection with the manuscript's exact
row-slice sample space, and the associated complex vectors agree
coordinate by coordinate.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace CircularLaw

def bernoulliSupport {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = true)

def bernoulliSupportSize {n : ℕ} (x : Fin n → Bool) : ℕ := (bernoulliSupport x).card

def rowSliceBoolRow {n d : ℕ} (s : RowSlice n d) : Fin n → Bool :=
  fun i => decide (i ∈ s.val)

theorem bernoulliSupport_rowSliceBoolRow {n d : ℕ} (s : RowSlice n d) :
    bernoulliSupport (rowSliceBoolRow s) = s.val := by
  ext i
  simp [bernoulliSupport, rowSliceBoolRow]

theorem rowSliceBoolRow_support {n : ℕ} (x : Fin n → Bool) :
    rowSliceBoolRow (⟨bernoulliSupport x, rfl⟩ : RowSlice n (bernoulliSupportSize x)) = x := by
  funext i
  simp only [rowSliceBoolRow, bernoulliSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  cases x i <;> simp

theorem rowSliceBoolRow_injective {n d : ℕ} : Function.Injective (@rowSliceBoolRow n d) := by
  intro s t h
  apply Subtype.ext
  simpa only [bernoulliSupport_rowSliceBoolRow] using congrArg bernoulliSupport h

def bernoulliSliceFiberEquiv (n d : ℕ) :
    RowSlice n d ≃ {x : Fin n → Bool // bernoulliSupportSize x = d} where
  toFun s := ⟨rowSliceBoolRow s, by
    rw [bernoulliSupportSize, bernoulliSupport_rowSliceBoolRow]
    exact s.property⟩
  invFun x := ⟨bernoulliSupport x.val, x.property⟩
  left_inv s := Subtype.ext (bernoulliSupport_rowSliceBoolRow s)
  right_inv x := by
    apply Subtype.ext
    exact rowSliceBoolRow_support x.val

theorem card_bernoulliSliceFiber (n d : ℕ) :
    Fintype.card {x : Fin n → Bool // bernoulliSupportSize x = d} = n.choose d := by
  rw [← Fintype.card_congr (bernoulliSliceFiberEquiv n d), card_rowSlice]

theorem bernoulliCubeVector_rowSliceBoolRow {n d : ℕ} (s : RowSlice n d) :
    bernoulliCubeVector (rowSliceBoolRow s) = WithLp.toLp 2 (rowEntry s) := by
  ext i
  simp only [bernoulliCubeVector, rowSliceBoolRow, rowEntry]
  by_cases h : i ∈ s.val <;> simp [h]

theorem bernoulliCoordinateLaw_singleton_real (p : ℝ≥0) (hp : p ≤ 1) (b : Bool) :
    (bernoulliCoordinateLaw p hp).real {b} = if b = true then (p : ℝ) else 1 - (p : ℝ) := by
  rw [measureReal_def, bernoulliCoordinateLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
  cases b with
  | false =>
    simp only [PMF.bernoulli_apply, Bool.cond_false, Bool.false_eq_true, if_false]
    rw [ENNReal.coe_toReal, NNReal.coe_sub hp, NNReal.coe_one]
  | true => simp [PMF.bernoulli_apply]

theorem bernoulliCubeLaw_singleton_real {n : ℕ} (p : ℝ≥0) (hp : p ≤ 1) (x : Fin n → Bool) :
    (bernoulliCubeLaw (Fin n) p hp).real {x} =
      (p : ℝ) ^ bernoulliSupportSize x * (1 - (p : ℝ)) ^ (n - bernoulliSupportSize x) := by
  rw [measureReal_def, bernoulliCubeLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, bernoulliCoordinateLaw_singleton_real]
  rw [Finset.prod_ite]
  have hFalse : (Finset.univ.filter (fun i => ¬ x i = true)) =
      Finset.univ \ bernoulliSupport x := by
    ext i
    simp [bernoulliSupport]
  rw [hFalse, Finset.prod_const, Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp only [bernoulliSupportSize, bernoulliSupport, Finset.card_univ, Fintype.card_fin]

end CircularLaw
