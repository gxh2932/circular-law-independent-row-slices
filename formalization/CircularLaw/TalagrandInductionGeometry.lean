import CircularLaw.TalagrandGeometry
import Mathlib.Algebra.BigOperators.Fin

/-!
# The geometric recursion in Talagrand's dimension induction

A slice contributes a zero disagreement in the new coordinate. A
projection witness can be lifted with a disagreement in `[0,1]`. Mixing
these two actual convex-hull witnesses gives the squared-distance
recursion required by the product-measure argument.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

variable {n : ℕ} {α : Type*}

def talagrandSlice (A : Set (Fin (n + 1) → α)) (t : α) : Set (Fin n → α) :=
  {y | Fin.cons t y ∈ A}

def talagrandProjection (A : Set (Fin (n + 1) → α)) : Set (Fin n → α) :=
  {y | ∃ t, Fin.cons t y ∈ A}

def talagrandConsMask (q : ℝ) (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cons q v.ofLp)

@[simp] theorem talagrandConsMask_zero (q : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    talagrandConsMask q v 0 = q := by simp [talagrandConsMask]

@[simp] theorem talagrandConsMask_succ (q : ℝ) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    talagrandConsMask q v i.succ = v i := by simp [talagrandConsMask]

theorem talagrandMask_cons (t s : α) (x y : Fin n → α) :
    talagrandMask (Fin.cons t x) (Fin.cons s y) =
      talagrandConsMask (if t = s then 0 else 1) (talagrandMask x y) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem talagrandConsMask_norm_sq (q : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    ‖talagrandConsMask q v‖ ^ 2 = q ^ 2 + ‖v‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, talagrandConsMask_zero,
    talagrandConsMask_succ, Real.norm_eq_abs, sq_abs]

theorem talagrandConsMask_combination (a b q r : ℝ) (u v : EuclideanSpace ℝ (Fin n)) :
    a • talagrandConsMask q u + b • talagrandConsMask r v =
      talagrandConsMask (a * q + b * r) (a • u + b • v) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem talagrandConsMask_weighted_sum {β : Type*} [Fintype β]
    (w q : β → ℝ) (v : β → EuclideanSpace ℝ (Fin n)) :
    ∑ j, w j • talagrandConsMask (q j) (v j) =
      talagrandConsMask (∑ j, w j * q j) (∑ j, w j • v j) := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i <;>
    simp [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul]

theorem talagrandProjection_nonempty {A : Set (Fin (n + 1) → α)} (hA : A.Nonempty) :
    (talagrandProjection A).Nonempty := by
  obtain ⟨y, hy⟩ := hA
  exact ⟨Fin.tail y, y 0, by simpa only [Fin.cons_self_tail] using hy⟩

theorem talagrandSlice_subset_projection (A : Set (Fin (n + 1) → α)) (t : α) :
    talagrandSlice A t ⊆ talagrandProjection A := fun _ hy => ⟨t, hy⟩

theorem talagrandMaskHull_lift_slice {A : Set (Fin (n + 1) → α)} {t : α} {x : Fin n → α}
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ talagrandMaskHull (talagrandSlice A t) x) :
    talagrandConsMask 0 u ∈ talagrandMaskHull A (Fin.cons t x) := by
  obtain ⟨β, hβ, w, y, hw, hSum, hy, hEq⟩ := talagrandMaskHull_weights hu
  letI := hβ
  have hFull : (∑ j, w j • talagrandMask (Fin.cons t x) (Fin.cons t (y j))) ∈
      talagrandMaskHull A (Fin.cons t x) :=
    (convex_convexHull ℝ _).sum_mem (fun j _ => hw j) hSum
      (fun j _ => subset_convexHull ℝ _ ⟨Fin.cons t (y j), hy j, rfl⟩)
  simpa [talagrandMask_cons, talagrandConsMask_weighted_sum, hEq] using hFull

theorem talagrandMaskHull_lift_projection {A : Set (Fin (n + 1) → α)} (t : α) {x : Fin n → α}
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ talagrandMaskHull (talagrandProjection A) x) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
      talagrandConsMask q v ∈ talagrandMaskHull A (Fin.cons t x) := by
  obtain ⟨β, hβ, w, y, hw, hSum, hy, hEq⟩ := talagrandMaskHull_weights hv
  letI := hβ
  choose s hs using hy
  let q : ℝ := ∑ j, w j * (if t = s j then 0 else 1)
  have hNonneg : 0 ≤ q := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (hw j) (by split_ifs <;> norm_num))
  have hUpper : q ≤ 1 := by
    rw [← hSum]
    apply Finset.sum_le_sum
    intro j _
    split_ifs <;> simp [hw j]
  have hFull : (∑ j, w j • talagrandMask (Fin.cons t x) (Fin.cons (s j) (y j))) ∈
      talagrandMaskHull A (Fin.cons t x) :=
    (convex_convexHull ℝ _).sum_mem (fun j _ => hw j) hSum
      (fun j _ => subset_convexHull ℝ _ ⟨Fin.cons (s j) (y j), hs j, rfl⟩)
  refine ⟨q, hNonneg, hUpper, ?_⟩
  simpa only [talagrandMask_cons, talagrandConsMask_weighted_sum, hEq] using hFull

theorem euclidean_squared_norm_combination_le {u v : EuclideanSpace ℝ (Fin n)}
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖a • u + (1 - a) • v‖ ^ 2 ≤ a * ‖u‖ ^ 2 + (1 - a) * ‖v‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, Real.norm_eq_abs, sq_abs]
  calc
    ∑ i, (a * u i + (1 - a) * v i) ^ 2 ≤ ∑ i, (a * (u i) ^ 2 + (1 - a) * (v i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_nonneg (mul_nonneg ha (sub_nonneg.mpr ha1)) (sq_nonneg (u i - v i))
      nlinarith
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem talagrandConvexDistance_projection_recursion {A : Set (Fin (n + 1) → α)}
    (hProjection : (talagrandProjection A).Nonempty) (t : α) (x : Fin n → α) :
    talagrandConvexDistance A (Fin.cons t x) ^ 2 ≤
      1 + talagrandConvexDistance (talagrandProjection A) x ^ 2 := by
  obtain ⟨v, hv, hDist⟩ := talagrandConvexDistance_attained hProjection x
  obtain ⟨q, hq0, hq1, hFull⟩ := talagrandMaskHull_lift_projection t hv
  have hLe : talagrandConvexDistance A (Fin.cons t x) ≤ ‖talagrandConsMask q v‖ := by
    simpa only [talagrandConvexDistance, dist_zero_left] using
      Metric.infDist_le_dist_of_mem (x := (0 : EuclideanSpace ℝ (Fin (n + 1)))) hFull
  have hSquare := pow_le_pow_left₀ (talagrandConvexDistance_nonneg A _) hLe 2
  rw [talagrandConsMask_norm_sq] at hSquare
  rw [hDist]
  nlinarith

theorem talagrandConvexDistance_slice_recursion {A : Set (Fin (n + 1) → α)}
    {t : α} (hSlice : (talagrandSlice A t).Nonempty) (x : Fin n → α)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    talagrandConvexDistance A (Fin.cons t x) ^ 2 ≤
      (1 - a) ^ 2 + a * talagrandConvexDistance (talagrandSlice A t) x ^ 2 +
        (1 - a) * talagrandConvexDistance (talagrandProjection A) x ^ 2 := by
  have hProjection : (talagrandProjection A).Nonempty :=
    hSlice.mono (talagrandSlice_subset_projection A t)
  obtain ⟨u, hu, hDistU⟩ := talagrandConvexDistance_attained hSlice x
  obtain ⟨v, hv, hDistV⟩ := talagrandConvexDistance_attained hProjection x
  obtain ⟨q, hq0, hq1, hLiftV⟩ := talagrandMaskHull_lift_projection t hv
  have hLiftU := talagrandMaskHull_lift_slice hu
  have hFull := (convex_convexHull ℝ (talagrandMaskSet A (Fin.cons t x)))
    hLiftU hLiftV ha (sub_nonneg.mpr ha1) (by ring : a + (1 - a) = 1)
  rw [talagrandConsMask_combination, mul_zero, zero_add] at hFull
  have hLe : talagrandConvexDistance A (Fin.cons t x) ≤
      ‖talagrandConsMask ((1 - a) * q) (a • u + (1 - a) • v)‖ := by
    simpa only [talagrandConvexDistance, dist_zero_left] using
      Metric.infDist_le_dist_of_mem (x := (0 : EuclideanSpace ℝ (Fin (n + 1)))) hFull
  have hSquare := pow_le_pow_left₀ (talagrandConvexDistance_nonneg A _) hLe 2
  rw [talagrandConsMask_norm_sq] at hSquare
  have hNorm := euclidean_squared_norm_combination_le (u := u) (v := v) ha ha1
  rw [hDistU, hDistV]
  have hHead : ((1 - a) * q) ^ 2 ≤ (1 - a) ^ 2 := by
    apply pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr ha1) hq0)
    nlinarith
  linarith

end CircularLaw
