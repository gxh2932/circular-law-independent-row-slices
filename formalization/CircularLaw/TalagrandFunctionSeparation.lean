import CircularLaw.TalagrandGeometry
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Convex sublevel sets and Talagrand separation

This is the deterministic bridge to concentration for the manuscript's
convex one-Lipschitz functions of bounded complex coordinates. No
probabilistic concentration input is assumed in these geometric results.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

variable {ι : Type*} [Fintype ι]

def complexCoordinateCube (K : ℝ) : Set (ι → ℂ) := {x | ∀ i, ‖x i‖ ≤ K}

def complexEuclideanSublevel (F : EuclideanSpace ℂ ι → ℝ) (K s : ℝ) : Set (ι → ℂ) :=
  complexCoordinateCube K ∩ {x | F (WithLp.toLp 2 x) ≤ s}

omit [Fintype ι] in
theorem complexCoordinateCube_convex (K : ℝ) : Convex ℝ (complexCoordinateCube (ι := ι) K) := by
  intro x hx y hy a b ha hb hab i
  calc
    ‖(a • x + b • y) i‖ ≤ ‖a • x i‖ + ‖b • y i‖ := norm_add_le _ _
    _ = a * ‖x i‖ + b * ‖y i‖ := by simp only [norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * K + b * K := add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
      (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = K := by rw [← add_mul, hab, one_mul]

theorem complexEuclideanSublevel_convex {F : EuclideanSpace ℂ ι → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (K s : ℝ) : Convex ℝ (complexEuclideanSublevel F K s) := by
  intro x hx y hy a b ha hb hab
  constructor
  · exact complexCoordinateCube_convex K hx.1 hy.1 ha hb hab
  · have hConvex := hF.2 (Set.mem_univ (WithLp.toLp 2 x))
      (Set.mem_univ (WithLp.toLp 2 y)) ha hb hab
    change F (a • WithLp.toLp 2 x + b • WithLp.toLp 2 y) ≤ s
    have hX := mul_le_mul_of_nonneg_left hx.2 ha
    have hY := mul_le_mul_of_nonneg_left hy.2 hb
    simp only [smul_eq_mul] at hConvex
    have hTotal : a * s + b * s = s := by rw [← add_mul, hab, one_mul]
    linarith

theorem convex_lipschitz_sublevel_separation {F : EuclideanSpace ℂ ι → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hLip : LipschitzWith 1 F)
    {K s t : ℝ} (hK : 0 ≤ K) {x : ι → ℂ} (hx : x ∈ complexCoordinateCube K)
    (hNonempty : (complexEuclideanSublevel F K s).Nonempty)
    (hHigh : s + t ≤ F (WithLp.toLp 2 x)) :
    t ≤ 2 * K * talagrandConvexDistance (complexEuclideanSublevel F K s) x := by
  obtain ⟨y, hy, hNorm⟩ := talagrand_euclidean_distance_le hNonempty
    (complexEuclideanSublevel_convex hF K s) hK hx (fun y hy => hy.1)
  have hDifference : F (WithLp.toLp 2 x) - F (WithLp.toLp 2 y) ≤
      ‖WithLp.toLp 2 (x - y)‖ := by
    have h := hLip.dist_le_mul (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simp only [NNReal.coe_one, one_mul, dist_eq_norm] at h
    exact (le_abs_self _).trans h
  have hLow : F (WithLp.toLp 2 y) ≤ s := hy.2
  linarith

theorem convex_lipschitz_sublevel_distance_lower {F : EuclideanSpace ℂ ι → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hLip : LipschitzWith 1 F)
    {K s t : ℝ} (hK : 0 < K) {x : ι → ℂ} (hx : x ∈ complexCoordinateCube K)
    (hNonempty : (complexEuclideanSublevel F K s).Nonempty)
    (hHigh : s + t ≤ F (WithLp.toLp 2 x)) :
    t / (2 * K) ≤ talagrandConvexDistance (complexEuclideanSublevel F K s) x :=
  (div_le_iff₀ (by positivity : 0 < 2 * K)).mpr
    (by simpa only [mul_comm] using convex_lipschitz_sublevel_separation hF hLip hK.le hx hNonempty hHigh)

end CircularLaw
