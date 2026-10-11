import CircularLaw.TalagrandFiniteMoment
import CircularLaw.TalagrandMaskTransport
import CircularLaw.TalagrandFunctionSeparation

/-!
# Convex concentration for arbitrary finite complex product laws

The two-event separation bound has absolute exponent `1/256`. The alphabet
map need not be injective, so repeated complex values and zero-weight
outcomes are allowed. No tail bound is left as an assumption.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

variable {α : Type*} [Fintype α] {n : ℕ}

theorem finiteProductEventMass_mul_le_expectation {μ : Fin n → α → ℝ}
    (hμ : ∀ i t, 0 ≤ μ i t) {B : Set (Fin n → α)} {f : (Fin n → α) → ℝ}
    (hf : ∀ x, 0 ≤ f x) {q : ℝ} (hB : ∀ x ∈ B, q ≤ f x) :
    q * finiteProductEventMass μ B ≤ finiteProductExpectation μ f := by
  rw [finiteProductEventMass, ← finiteProductExpectation_const_mul]
  apply finiteProductExpectation_mono hμ
  intro x
  by_cases hx : x ∈ B
  · simpa only [if_pos hx, mul_one] using hB x hx
  · simpa only [if_neg hx, mul_zero] using hf x

theorem finiteProductExpectation_add (μ : Fin n → α → ℝ) (f g : (Fin n → α) → ℝ) :
    finiteProductExpectation μ (fun x => f x + g x) =
      finiteProductExpectation μ f + finiteProductExpectation μ g := by
  simp only [finiteProductExpectation, mul_add, Finset.sum_add_distrib]

theorem finiteProductEventMass_union_le {μ : Fin n → α → ℝ} (hμ : ∀ i t, 0 ≤ μ i t)
    (A B : Set (Fin n → α)) :
    finiteProductEventMass μ (A ∪ B) ≤ finiteProductEventMass μ A + finiteProductEventMass μ B := by
  rw [finiteProductEventMass, finiteProductEventMass, finiteProductEventMass,
    ← finiteProductExpectation_add]
  apply finiteProductExpectation_mono hμ
  intro x
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> simp [hA, hB]

theorem talagrand_finite_convex_two_events {μ : Fin n → α → ℝ}
    (hμ : ∀ i a, 0 ≤ μ i a) (hNorm : ∀ i, ∑ a, μ i a = 1)
    (e : α → ℂ) {K : ℝ} (hK : 0 < K) (hBound : ∀ a, ‖e a‖ ≤ K)
    {F : EuclideanSpace ℂ (Fin n) → ℝ} (hF : ConvexOn ℝ Set.univ F) (hLip : LipschitzWith 1 F)
    (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    finiteProductEventMass μ {x | F (WithLp.toLp 2 (talagrandCoordinateMap e x)) ≤ s} *
      finiteProductEventMass μ {x | s + t * K ≤ F (WithLp.toLp 2 (talagrandCoordinateMap e x))} ≤
        Real.exp (-t ^ 2 / 256) := by
  let A : Set (Fin n → α) := {x | F (WithLp.toLp 2 (talagrandCoordinateMap e x)) ≤ s}
  let B : Set (Fin n → α) := {x | s + t * K ≤ F (WithLp.toLp 2 (talagrandCoordinateMap e x))}
  let p := finiteProductEventMass μ A
  by_cases hp : 0 < p
  · have hA := finiteProductEventMass_pos_nonempty hp
    have hImage : talagrandCoordinateMap e '' A ⊆ complexEuclideanSublevel F K s := by
      rintro z ⟨x, hx, rfl⟩
      exact ⟨fun i => hBound (x i), hx⟩
    have hSublevel := (hA.image (talagrandCoordinateMap e)).mono hImage
    have hPointwise (x : Fin n → α) (hx : x ∈ B) :
        Real.exp (t ^ 2 / 256) ≤ Real.exp (talagrandConvexDistance A x ^ 2 / 64) := by
      have hSeparation := convex_lipschitz_sublevel_separation hF hLip hK.le
        (fun i => hBound (x i)) hSublevel hx
      have hDist := (talagrandConvexDistance_mono (hA.image (talagrandCoordinateMap e)) hImage
        (talagrandCoordinateMap e x)).trans (talagrandConvexDistance_map_le e hA x)
      have hScale : t * K ≤ 2 * K * talagrandConvexDistance A x := hSeparation.trans
        (mul_le_mul_of_nonneg_left hDist (by positivity : 0 ≤ 2 * K))
      have hT : t ≤ 2 * talagrandConvexDistance A x := by nlinarith
      have hSq := pow_le_pow_left₀ ht hT 2
      apply Real.exp_le_exp.mpr
      nlinarith
    have hMarkov := finiteProductEventMass_mul_le_expectation hμ
      (fun x => (Real.exp_pos (talagrandConvexDistance A x ^ 2 / 64)).le) hPointwise
    have hMoment := talagrand_finite_product_moment hμ hNorm A hp
    have hProduct : Real.exp (t ^ 2 / 256) * (p * finiteProductEventMass μ B) ≤ 1 := by
      have h := (le_div_iff₀ hp).mp (hMarkov.trans hMoment)
      nlinarith
    calc
      p * finiteProductEventMass μ B ≤ 1 / Real.exp (t ^ 2 / 256) :=
        (le_div_iff₀ (Real.exp_pos _)).mpr (by nlinarith)
      _ = Real.exp (-t ^ 2 / 256) := by rw [one_div, ← Real.exp_neg]; congr 1; ring
  · have hpZero : p = 0 := le_antisymm (le_of_not_gt hp) (finiteProductEventMass_nonneg hμ A)
    change p * finiteProductEventMass μ B ≤ _
    rw [hpZero, zero_mul]
    exact (Real.exp_pos _).le

theorem talagrand_finite_convex_median_tail {μ : Fin n → α → ℝ}
    (hμ : ∀ i a, 0 ≤ μ i a) (hNorm : ∀ i, ∑ a, μ i a = 1)
    (e : α → ℂ) {K : ℝ} (hK : 0 < K) (hBound : ∀ a, ‖e a‖ ≤ K)
    {F : EuclideanSpace ℂ (Fin n) → ℝ} (hF : ConvexOn ℝ Set.univ F) (hLip : LipschitzWith 1 F)
    (m : ℝ) (hLower : 1 / 2 ≤ finiteProductEventMass μ
      {x | F (WithLp.toLp 2 (talagrandCoordinateMap e x)) ≤ m})
    (hUpper : 1 / 2 ≤ finiteProductEventMass μ
      {x | m ≤ F (WithLp.toLp 2 (talagrandCoordinateMap e x))})
    {t : ℝ} (ht : 0 ≤ t) :
    finiteProductEventMass μ {x | t * K ≤ |F (WithLp.toLp 2 (talagrandCoordinateMap e x)) - m|} ≤
      4 * Real.exp (-t ^ 2 / 256) := by
  let G := fun x => F (WithLp.toLp 2 (talagrandCoordinateMap e x))
  have hHigh : finiteProductEventMass μ {x | m + t * K ≤ G x} ≤ 2 * Real.exp (-t ^ 2 / 256) := by
    have h := talagrand_finite_convex_two_events hμ hNorm e hK hBound hF hLip m ht
    have hNonneg := finiteProductEventMass_nonneg hμ {x | m + t * K ≤ G x}
    nlinarith [mul_le_mul_of_nonneg_right hLower hNonneg]
  have hLow : finiteProductEventMass μ {x | G x ≤ m - t * K} ≤ 2 * Real.exp (-t ^ 2 / 256) := by
    have h := talagrand_finite_convex_two_events hμ hNorm e hK hBound hF hLip (m - t * K) ht
    have hCutoff : {x | m - t * K + t * K ≤ F (WithLp.toLp 2 (talagrandCoordinateMap e x))} =
        {x | m ≤ G x} := by ext x; simp only [sub_add_cancel, G]
    rw [hCutoff] at h
    have hNonneg := finiteProductEventMass_nonneg hμ {x | G x ≤ m - t * K}
    nlinarith [mul_le_mul_of_nonneg_left hUpper hNonneg]
  have hCover : {x | t * K ≤ |G x - m|} ⊆ {x | G x ≤ m - t * K} ∪ {x | m + t * K ≤ G x} := by
    intro x hx
    change t * K ≤ |G x - m| at hx
    by_cases hSign : 0 ≤ G x - m
    · right
      change m + t * K ≤ G x
      rw [abs_of_nonneg hSign] at hx
      linarith
    · left
      change G x ≤ m - t * K
      rw [abs_of_nonpos (le_of_not_ge hSign)] at hx
      linarith
  have hUnion := finiteProductEventMass_union_le hμ {x | G x ≤ m - t * K} {x | m + t * K ≤ G x}
  exact (finiteProductEventMass_mono hμ hCover).trans (hUnion.trans (by linarith))

end CircularLaw
