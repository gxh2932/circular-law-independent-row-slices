import CircularLaw.GaussianOrderCombinations
import CircularLaw.ComplexSphereGrid
import CircularLaw.GaussianCoordinateTails
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Uniform Gaussian non-flatness through an actual sphere net

The order-statistic bad event for some unit coefficient is closed by
compact projection. A deterministic coordinate bound transfers it to the
explicit finite sphere grid; the actual-copy coordinate tail handles the
remaining error event.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem gaussianCopiesCombination_joint_continuous {X : Type*} [TopologicalSpace X]
    {n p : ℕ} (Y : X → Fin p → EuclideanSpace ℂ (Fin n))
    (hY : ∀ k, Continuous (fun z => Y z k)) :
    Continuous (fun q : X × EuclideanSpace ℂ (Fin p) => gaussianCopiesCombination (Y q.1) q.2) := by
  simp_rw [gaussianCopiesCombination_apply]
  apply continuous_finset_sum
  intro k _
  exact ((PiLp.continuous_apply 2 (fun _ : Fin p => ℂ) k).comp continuous_snd).smul
    ((hY k).comp continuous_fst)

theorem gaussianCopiesCombination_nonflat_isClosed {X : Type*} [TopologicalSpace X]
    {n p : ℕ} (Y : X → Fin p → EuclideanSpace ℂ (Fin n))
    (hY : ∀ k, Continuous (fun z => Y z k)) (r : ℕ) (τ : ℝ) :
    IsClosed {z | ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
      orderedNormAt (fun i => gaussianCopiesCombination (Y z) x i) r ≤ τ} := by
  let S := Metric.sphere (0 : EuclideanSpace ℂ (Fin p)) 1
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let F : Set (X × S) := {q | orderedNormAt
    (fun i => gaussianCopiesCombination (Y q.1) (q.2 : EuclideanSpace ℂ (Fin p)) i) r ≤ τ}
  have hClosed : IsClosed F := isClosed_le
    ((orderedNormAt_euclidean_continuous r).comp
      ((gaussianCopiesCombination_joint_continuous Y hY).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))) continuous_const
  have hEq : Prod.fst '' F = {z | ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
      orderedNormAt (fun i => gaussianCopiesCombination (Y z) x i) r ≤ τ} := by
    ext z
    constructor
    · rintro ⟨⟨z, x⟩, hF, rfl⟩
      refine ⟨x, ?_, hF⟩
      simpa only [S, Metric.mem_sphere, dist_zero_right] using x.property
    · rintro ⟨x, hx, hSmall⟩
      have hxS : x ∈ S := by simpa only [S, Metric.mem_sphere, dist_zero_right] using hx
      exact ⟨(z, ⟨x, hxS⟩), hSmall, rfl⟩
  rw [← hEq]
  exact isClosedMap_fst_of_compactSpace F hClosed

theorem projectedGaussianCopies_uniform_nonflat_measurableSet {n p : ℕ}
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (r : ℕ) (τ : ℝ) :
    MeasurableSet {z | ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
      orderedNormAt (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i) r ≤ τ} :=
  (gaussianCopiesCombination_nonflat_isClosed (projectedGaussianCopies E)
    (projectedGaussianCopies_continuous E) r τ).measurableSet

theorem gaussianCopiesCombination_coordinate_difference_bound {n p : ℕ}
    (Y : Fin p → EuclideanSpace ℂ (Fin n)) (x y : EuclideanSpace ℂ (Fin p))
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hY : ∀ k, ‖Y k i‖ ≤ R) :
    ‖gaussianCopiesCombination Y x i - gaussianCopiesCombination Y y i‖ ≤
      ‖x - y‖ * (Real.sqrt p * R) := by
  have hEq : gaussianCopiesCombination Y x i - gaussianCopiesCombination Y y i =
      gaussianCopiesCombination Y (x - y) i := by rw [map_sub]; rfl
  have hSum : (∑ k : Fin p, ‖Y k i‖ ^ 2) ≤ (p : ℝ) * R ^ 2 := by
    calc
      _ ≤ ∑ _k : Fin p, R ^ 2 := Finset.sum_le_sum
        (fun k _ => (sq_le_sq₀ (norm_nonneg _) hR).mpr (hY k))
      _ = _ := by simp
  rw [hEq]
  calc
    _ ≤ ‖x - y‖ * Real.sqrt (∑ k, ‖Y k i‖ ^ 2) :=
      gaussianCopiesCombination_coordinate_norm_bound Y (x - y) i
    _ ≤ ‖x - y‖ * Real.sqrt ((p : ℝ) * R ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hSum) (norm_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg p), Real.sqrt_sq hR]

theorem gaussianCopiesCombination_nonflat_net_reduction {n p r : ℕ}
    (hr : 0 < r) (hrn : r ≤ n) (Y : Fin p → EuclideanSpace ℂ (Fin n))
    (S : Finset (EuclideanSpace ℂ (Fin p))) {δ R τ a : ℝ} (hR : 0 ≤ R)
    (hCover : ∀ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 → ∃ y ∈ S, ‖x - y‖ ≤ δ)
    (hBudget : δ * (Real.sqrt p * R) ≤ a)
    (hBad : ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
      orderedNormAt (fun i => gaussianCopiesCombination Y x i) r ≤ τ) :
    (∃ k : Fin p, ∃ i : Fin n, R ≤ ‖Y k i‖) ∨
      ∃ y ∈ S, orderedNormAt (fun i => gaussianCopiesCombination Y y i) r ≤ τ + a := by
  by_cases hLarge : ∃ k : Fin p, ∃ i : Fin n, R ≤ ‖Y k i‖
  · exact Or.inl hLarge
  · right
    obtain ⟨x, hx, hSmall⟩ := hBad
    obtain ⟨y, hy, hDist⟩ := hCover x hx
    refine ⟨y, hy, ?_⟩
    have hPointwise : ∀ i, ‖gaussianCopiesCombination Y y i - gaussianCopiesCombination Y x i‖ ≤ a := by
      intro i
      apply (gaussianCopiesCombination_coordinate_difference_bound Y y x i hR
        (fun k => (lt_of_not_ge (fun h => hLarge ⟨k, i, h⟩)).le)).trans
      rw [norm_sub_rev]
      exact (mul_le_mul_of_nonneg_right hDist (by positivity)).trans hBudget
    have hOrder := (orderedNormAt_perturbation
      (fun i => gaussianCopiesCombination Y x i) (fun i => gaussianCopiesCombination Y y i)
        hr hrn a hPointwise).1
    exact hOrder.trans (add_le_add_left hSmall _)

theorem projectedGaussianCopies_uniform_nonflat_net_bound {n p m : ℕ}
    (hn : 0 < n) (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (hm : m ≤ Module.finrank ℂ Eᗮ) (hLarge : 512 ≤ m)
    (S : Finset (EuclideanSpace ℂ (Fin p))) (hS : ∀ x ∈ S, ‖x‖ = 1)
    {δ R : ℝ} (hR : 0 < R)
    (hCover : ∀ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 → ∃ y ∈ S, ‖x - y‖ ≤ δ)
    (hBudget : δ * (Real.sqrt p * R) ≤ (m : ℝ) / (1024 * n)) :
    (standardGaussianCopiesLaw n p).real
      {z | ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
        orderedNormAt (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i)
          (m / 512) ≤ (m : ℝ) / (1024 * n)} ≤
      (p : ℝ) * n * Real.exp (-R ^ 2) + (S.card : ℝ) * Real.exp (-(m : ℝ) / 512) := by
  have hmn : m ≤ n := hm.trans (by simpa using Eᗮ.finrank_le)
  have hr : 0 < m / 512 := by omega
  have hrn : m / 512 ≤ n := by omega
  have hTwice : (m : ℝ) / (1024 * n) + (m : ℝ) / (1024 * n) =
      (m : ℝ) / (512 * n) := by ring
  have hSubset : {z | ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
      orderedNormAt (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i)
        (m / 512) ≤ (m : ℝ) / (1024 * n)} ⊆
      {z | ∃ k : Fin p, ∃ i : Fin n, R ≤ ‖projectedGaussianCopies E z k i‖} ∪
      {z | ∃ y ∈ S, orderedNormAt
        (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) y i) (m / 512) ≤
          (m : ℝ) / (512 * n)} := by
    intro z hz
    have h := gaussianCopiesCombination_nonflat_net_reduction hr hrn
      (projectedGaussianCopies E z) S hR.le hCover hBudget hz
    simpa only [hTwice, Set.mem_union, Set.mem_setOf_eq] using h
  apply (measureReal_mono hSubset).trans
  apply (measureReal_union_le _ _).trans
  exact add_le_add (projectedGaussianCopies_any_coordinate_tail E hR)
    (projectedGaussianCopiesCombination_finite_unit_nonflat_smallBall hn E hm hLarge S hS)

def gaussianNonflatGridResolution (n p : ℕ) : ℕ := 4096 * p ^ 2 * n ^ 2

theorem gaussianNonflatGridResolution_large {n p : ℕ} (hn : 0 < n) (hp : 0 < p) :
    8 * p ≤ gaussianNonflatGridResolution n p := by
  have hpSq : p ≤ p ^ 2 := by nlinarith
  have hnSq : 1 ≤ n ^ 2 := by nlinarith
  have hMul := Nat.mul_le_mul_left (4096 * p ^ 2) hnSq
  unfold gaussianNonflatGridResolution
  nlinarith

theorem gaussianNonflatGridResolution_error_budget {n p m : ℕ}
    (hn : 0 < n) (hp : 0 < p) (hm : 1 ≤ m) :
    (4 * (p : ℝ) / gaussianNonflatGridResolution n p) * (Real.sqrt p * n) ≤
      (m : ℝ) / (1024 * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpSqrt : Real.sqrt p ≤ (p : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨hpR.le, by nlinarith⟩
  have hResolution : (gaussianNonflatGridResolution n p : ℝ) =
      4096 * (p : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
    simp only [gaussianNonflatGridResolution, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hResolutionPos : (0 : ℝ) < gaussianNonflatGridResolution n p := by
    rw [hResolution]
    positivity
  calc
    _ ≤ (4 * (p : ℝ) / gaussianNonflatGridResolution n p) * ((p : ℝ) * n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpSqrt hnR.le) (by positivity)
    _ = 1 / (1024 * n) := by rw [hResolution]; field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right hmOne (by positivity)

theorem projectedGaussianCopies_uniform_nonflat_grid_bound {n p m : ℕ}
    (hn : 0 < n) (hp : 0 < p) (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (hm : m ≤ Module.finrank ℂ Eᗮ) (hLarge : 512 ≤ m) :
    (standardGaussianCopiesLaw n p).real
      {z | ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
        orderedNormAt (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i)
          (m / 512) ≤ (m : ℝ) / (1024 * n)} ≤
      (p : ℝ) * n * Real.exp (-(n : ℝ) ^ 2) +
        (2 * (gaussianNonflatGridResolution n p : ℝ) + 3) ^ (2 * p) *
          Real.exp (-(m : ℝ) / 512) := by
  let S := complexSphereGrid p (gaussianNonflatGridResolution n p)
  have hCard : (S.card : ℝ) ≤
      (2 * (gaussianNonflatGridResolution n p : ℝ) + 3) ^ (2 * p) := by
    exact_mod_cast complexSphereGrid_card_le p (gaussianNonflatGridResolution n p)
  have hBound := projectedGaussianCopies_uniform_nonflat_net_bound hn E hm hLarge S
    (fun x hx => complexSphereGrid_unit x hx) (by exact_mod_cast hn : (0 : ℝ) < n)
    (fun x hx => complexSphereGrid_cover hp (gaussianNonflatGridResolution_large hn hp) x hx)
    (gaussianNonflatGridResolution_error_budget hn hp (by omega : 1 ≤ m))
  exact hBound.trans (add_le_add_right
    (mul_le_mul_of_nonneg_right hCard (Real.exp_pos _).le) _)

end CircularLaw
