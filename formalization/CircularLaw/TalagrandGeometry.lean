import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-!
# Talagrand masks and their convex distance

The masks record exactly which coordinates disagree. Their convex hull is
compact even when the coordinate alphabet or the set of witnesses is infinite.
A nearest mask therefore exists for every nonempty set. Finite convex
combinations of masks give actual convex combinations of the witness points.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

variable {ι α : Type*} [Fintype ι]

def talagrandMask (x y : ι → α) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => if x i = y i then 0 else 1)

omit [Fintype ι] in
@[simp] theorem talagrandMask_apply (x y : ι → α) (i : ι) :
    talagrandMask x y i = if x i = y i then 0 else 1 := rfl

def talagrandMaskSet (A : Set (ι → α)) (x : ι → α) : Set (EuclideanSpace ℝ ι) :=
  talagrandMask x '' A

def talagrandMaskHull (A : Set (ι → α)) (x : ι → α) : Set (EuclideanSpace ℝ ι) :=
  convexHull ℝ (talagrandMaskSet A x)

def talagrandConvexDistance (A : Set (ι → α)) (x : ι → α) : ℝ :=
  Metric.infDist 0 (talagrandMaskHull A x)

theorem talagrandMaskSet_finite (A : Set (ι → α)) (x : ι → α) :
    (talagrandMaskSet A x).Finite := by
  let f : (ι → Bool) → EuclideanSpace ℝ ι :=
    fun b => WithLp.toLp 2 (fun i => if b i then 1 else 0)
  apply (Set.finite_range f).subset
  rintro v ⟨y, _, rfl⟩
  refine ⟨fun i => decide (x i ≠ y i), ?_⟩
  ext i
  by_cases h : x i = y i <;> simp [f, talagrandMask, h]

theorem talagrandMaskHull_compact (A : Set (ι → α)) (x : ι → α) :
    IsCompact (talagrandMaskHull A x) :=
  (talagrandMaskSet_finite A x).isCompact_convexHull

theorem talagrandMaskHull_nonempty {A : Set (ι → α)} (hA : A.Nonempty) (x : ι → α) :
    (talagrandMaskHull A x).Nonempty := by
  obtain ⟨y, hy⟩ := hA
  exact ⟨talagrandMask x y, subset_convexHull ℝ _ ⟨y, hy, rfl⟩⟩

theorem talagrandConvexDistance_nonneg (A : Set (ι → α)) (x : ι → α) :
    0 ≤ talagrandConvexDistance A x := Metric.infDist_nonneg

theorem talagrandConvexDistance_le_mask_norm {A : Set (ι → α)} {x y : ι → α}
    (hy : y ∈ A) : talagrandConvexDistance A x ≤ ‖talagrandMask x y‖ := by
  simpa only [talagrandConvexDistance, talagrandMaskHull, dist_zero_left] using Metric.infDist_le_dist_of_mem (x := (0 : EuclideanSpace ℝ ι))
    (subset_convexHull ℝ (talagrandMaskSet A x) ⟨y, hy, rfl⟩)

theorem talagrandConvexDistance_attained {A : Set (ι → α)} (hA : A.Nonempty) (x : ι → α) :
    ∃ v ∈ talagrandMaskHull A x, talagrandConvexDistance A x = ‖v‖ := by
  simpa only [talagrandConvexDistance, dist_zero_left] using
    (talagrandMaskHull_compact A x).exists_infDist_eq_dist (talagrandMaskHull_nonempty hA x) 0

omit [Fintype ι] in
@[simp] theorem talagrandMask_self (x : ι → α) : talagrandMask x x = 0 := by
  ext i
  simp

theorem talagrandConvexDistance_zero_of_mem {A : Set (ι → α)} {x : ι → α} (hx : x ∈ A) :
    talagrandConvexDistance A x = 0 := by
  apply le_antisymm _ (talagrandConvexDistance_nonneg A x)
  simpa only [talagrandMask_self, norm_zero] using talagrandConvexDistance_le_mask_norm (x := x) hx

theorem talagrandMaskHull_weights {A : Set (ι → α)} {x : ι → α}
    {v : EuclideanSpace ℝ ι} (hv : v ∈ talagrandMaskHull A x) :
    ∃ (β : Type) (_ : Fintype β) (w : β → ℝ) (y : β → (ι → α)),
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧ (∀ j, y j ∈ A) ∧
      ∑ j, w j • talagrandMask x (y j) = v := by
  obtain ⟨β, hβ, w, z, hw, hSum, hz, hEq⟩ := mem_convexHull_iff_exists_fintype.mp hv
  letI := hβ
  choose y hy hMask using hz
  refine ⟨β, hβ, w, y, hw, hSum, hy, ?_⟩
  simpa only [hMask] using hEq

theorem talagrandMaskHull_coordinate_nonneg {A : Set (ι → α)} {x : ι → α}
    {v : EuclideanSpace ℝ ι} (hv : v ∈ talagrandMaskHull A x) (i : ι) : 0 ≤ v i := by
  obtain ⟨β, hβ, w, y, hw, _, _, hEq⟩ := talagrandMaskHull_weights hv
  letI := hβ
  rw [← hEq]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, talagrandMask_apply]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (by split_ifs <;> norm_num))

theorem euclidean_norm_le_of_coordinate_domination {z : ι → ℂ} {v : EuclideanSpace ℝ ι}
    {a : ℝ} (ha : 0 ≤ a) (h : ∀ i, ‖z i‖ ≤ a * v i) :
    ‖WithLp.toLp 2 z‖ ≤ a * ‖v‖ := by
  have hSq : ‖WithLp.toLp 2 z‖ ^ 2 ≤ (a * ‖v‖) ^ 2 := by
    calc
      _ = ∑ i, ‖z i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
      _ ≤ ∑ i, (a * v i) ^ 2 := Finset.sum_le_sum (fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (h i) 2)
      _ = a ^ 2 * ∑ i, (v i) ^ 2 := by simp_rw [mul_pow]; rw [Finset.mul_sum]
      _ = (a * ‖v‖) ^ 2 := by
        rw [mul_pow, PiLp.norm_sq_eq_of_L2]
        simp only [Real.norm_eq_abs, sq_abs]
  have hRight : 0 ≤ a * ‖v‖ := mul_nonneg ha (norm_nonneg v)
  nlinarith [norm_nonneg (WithLp.toLp 2 z)]

theorem talagrandMaskHull_euclidean_witness {A : Set (ι → ℂ)} (hA : Convex ℝ A)
    {x : ι → ℂ} {K : ℝ} (hK : 0 ≤ K) (hx : ∀ i, ‖x i‖ ≤ K)
    (hBound : ∀ y ∈ A, ∀ i, ‖y i‖ ≤ K) {v : EuclideanSpace ℝ ι}
    (hv : v ∈ talagrandMaskHull A x) :
    ∃ y ∈ A, ‖WithLp.toLp 2 (x - y)‖ ≤ 2 * K * ‖v‖ := by
  obtain ⟨β, hβ, w, y, hw, hSum, hy, hEq⟩ := talagrandMaskHull_weights hv
  letI := hβ
  let z : ι → ℂ := ∑ j, w j • y j
  have hz : z ∈ A := hA.sum_mem (fun j _ => hw j) hSum (fun j _ => hy j)
  refine ⟨z, hz, euclidean_norm_le_of_coordinate_domination (by positivity)
    ?_⟩
  intro i
  have hDiff : x i - z i = ∑ j, w j • (x i - y j i) := by
    simp only [z, Finset.sum_apply, Pi.smul_apply]
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hSum, one_smul]
  have hCoord : ∑ j, w j * talagrandMask x (y j) i = v i := by
    simpa only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using congrArg (fun u => u i) hEq
  calc
    ‖x i - z i‖ = ‖∑ j, w j • (x i - y j i)‖ := congrArg norm hDiff
    _ ≤ ∑ j, ‖w j • (x i - y j i)‖ := norm_sum_le _ _
    _ = ∑ j, w j * ‖x i - y j i‖ := by simp only [norm_smul, Real.norm_of_nonneg (hw _)]
    _ ≤ ∑ j, w j * (2 * K * talagrandMask x (y j) i) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hw j)
      by_cases h : x i = y j i
      · simp [h]
      · simp only [talagrandMask_apply, h, if_false, mul_one]
        exact (norm_sub_le _ _).trans (by linarith [hx i, hBound (y j) (hy j) i])
    _ = 2 * K * v i := by rw [← hCoord, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

theorem talagrand_euclidean_distance_le {A : Set (ι → ℂ)} (hNonempty : A.Nonempty)
    (hA : Convex ℝ A) {x : ι → ℂ} {K : ℝ} (hK : 0 ≤ K) (hx : ∀ i, ‖x i‖ ≤ K)
    (hBound : ∀ y ∈ A, ∀ i, ‖y i‖ ≤ K) :
    ∃ y ∈ A, ‖WithLp.toLp 2 (x - y)‖ ≤ 2 * K * talagrandConvexDistance A x := by
  obtain ⟨v, hv, hDist⟩ := talagrandConvexDistance_attained hNonempty x
  obtain ⟨y, hy, hNorm⟩ := talagrandMaskHull_euclidean_witness hA hK hx hBound hv
  exact ⟨y, hy, hDist ▸ hNorm⟩

end CircularLaw
