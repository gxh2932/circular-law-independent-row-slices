import CircularLaw.ExposureProcessCompletion
import Mathlib.MeasureTheory.Function.Floor

/-!
# The half-integer form of SSS25 Lemma 8.4

The measurable doubled height is the natural floor of twice the height.
Half-integer valuedness proves exact reconstruction, so this change of
coordinates preserves the moving barrier and the conditional bad-step event.
-/

noncomputable section
open Classical MeasureTheory

namespace CircularLaw

def doubledExposureHeight {Ω : Type*} (Y : Ω → ℝ) : Ω → ℕ := fun x => ⌊2 * Y x⌋₊

theorem doubled_exposure_height_reconstruction {Ω : Type*} (Y : Ω → ℝ)
    (hHalf : ∀ x, ∃ h : ℕ, Y x = (h : ℝ) / 2) (x : Ω) :
    (doubledExposureHeight Y x : ℝ) = 2 * Y x := by
  obtain ⟨h, hh⟩ := hHalf x
  rw [doubledExposureHeight, hh, show 2 * ((h : ℝ) / 2) = (h : ℝ) by ring, Nat.floor_natCast]


theorem conditional_indicator_complement_eq_one_sub
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m0) {B : Set Ω}
    (hB : @MeasurableSet Ω m0 B) :
    ∀ᵐ x ∂μ, (μ[Bᶜ.indicator (fun _ => (1 : ℝ)) | m]) x =
      1 - (μ[B.indicator (fun _ => (1 : ℝ)) | m]) x := by
  have hFunction : Bᶜ.indicator (fun _ => (1 : ℝ)) =
      (fun _ => (1 : ℝ)) - B.indicator (fun _ => (1 : ℝ)) := by
    ext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [hFunction]
  have hSub := condExp_sub (μ := μ) (integrable_const (1 : ℝ)) ((integrable_const 1).indicator hB) m
  filter_upwards [hSub] with x hx
  simpa only [condExp_const hm, Pi.sub_apply] using hx

theorem half_integer_exposure_process_completion
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (T : ℕ)
    (hMeas : ∀ s, s ≤ T → Measurable[F s] (Y s))
    (hHalf : ∀ s, s ≤ T → ∀ x, ∃ h : ℕ, Y s x = (h : ℝ) / 2)
    (hInitial : ∀ x, Y 0 x ≤ (T : ℝ) / 8)
    (hGrowth : ∀ s, s < T → ∀ x, Y (s + 1) x ≤ Y s x + 1)
    {q : ℝ} (hq : 0 ≤ q)
    (hDrift : ∀ s, s < T → ∀ᵐ x ∂μ,
      (((T - s) / 16 : ℕ) : ℝ) ≤ Y s x →
      (μ[({y | Y s y - (if 0 < Y s y then (1 / 2 : ℝ) else 0) < Y (s + 1) y}).indicator
        (fun _ => (1 : ℝ)) | F s]) x ≤ q) :
    1 - 4 * q ^ (1 / 8 : ℝ) ≤ μ.real {x | Y T x = 0} := by
  let H := fun s => doubledExposureHeight (Y s)
  have hRepr : ∀ s, s ≤ T → ∀ x, (H s x : ℝ) = 2 * Y s x := by
    intro s hs x
    exact doubled_exposure_height_reconstruction (Y s) (hHalf s hs) x
  have hHMeas : ∀ s, s ≤ T → Measurable[F s] (H s) := by
    intro s hs
    letI : MeasurableSpace Ω := F s
    exact ((hMeas s hs).const_mul 2).nat_floor
  have hHInitial : ∀ x, (H 0 x : ℝ) ≤ (T : ℝ) / 4 := by
    intro x
    rw [hRepr 0 (by omega) x]
    have := hInitial x
    linarith
  have hHGrowth : ∀ s, s < T → ∀ x, H (s + 1) x ≤ H s x + 2 := by
    intro s hs x
    have hReal : (H (s + 1) x : ℝ) ≤ (H s x : ℝ) + 2 := by
      rw [hRepr (s + 1) (by omega) x, hRepr s (by omega) x]
      have := hGrowth s hs x
      linarith
    exact_mod_cast hReal
  have hEvents (s : ℕ) (hs : s < T) :
      {x | H s x - 1 < H (s + 1) x} =
        {x | Y s x - (if 0 < Y s x then (1 / 2 : ℝ) else 0) < Y (s + 1) x} := by
    ext x
    simp only [Set.mem_setOf_eq]
    have hOld := hRepr s (by omega) x
    have hNew := hRepr (s + 1) (by omega) x
    by_cases hZero : H s x = 0
    · have hYZero : Y s x = 0 := by rw [hZero, Nat.cast_zero] at hOld; linarith
      simp only [hZero, Nat.zero_sub, hYZero, lt_self_iff_false, if_false, sub_zero]
      constructor
      · intro hx
        have hCast : (0 : ℝ) < H (s + 1) x := by exact_mod_cast hx
        linarith
      · intro hx
        have hCast : (0 : ℝ) < H (s + 1) x := by linarith
        exact_mod_cast hCast
    · have hNat : 1 ≤ H s x := Nat.one_le_iff_ne_zero.mpr hZero
      have hCast : (1 : ℝ) ≤ H s x := by exact_mod_cast hNat
      have hYPos : 0 < Y s x := by linarith
      simp only [hYPos, if_true]
      have hSub : ((H s x - 1 : ℕ) : ℝ) = (H s x : ℝ) - 1 := by
        rw [Nat.cast_sub hNat, Nat.cast_one]
      constructor
      · intro hx
        have hCast : ((H s x - 1 : ℕ) : ℝ) < (H (s + 1) x : ℝ) := by exact_mod_cast hx
        rw [hSub] at hCast
        linarith
      · intro hx
        have hCast : ((H s x - 1 : ℕ) : ℝ) < (H (s + 1) x : ℝ) := by rw [hSub]; linarith
        exact_mod_cast hCast
  have hHDrift : ∀ s, s < T → ∀ᵐ x ∂μ,
      2 * ((T - s) / 16) ≤ H s x →
      (μ[({y | H s y - 1 < H (s + 1) y}).indicator (fun _ => (1 : ℝ)) | F s]) x ≤ q := by
    intro s hs
    filter_upwards [hDrift s hs] with x hx hActive
    rw [hEvents s hs]
    apply hx
    have hCast : 2 * ((((T - s) / 16 : ℕ) : ℝ)) ≤ H s x := by exact_mod_cast hActive
    rw [hRepr s (by omega) x] at hCast
    linarith
  have hBound := exposure_process_zero_height_probability_bound μ F H T hHMeas hHInitial hHGrowth hq hHDrift
  have hZeroEvent : {x | H T x = 0} = {x | Y T x = 0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    have h := hRepr T le_rfl x
    constructor
    · intro hx
      rw [hx, Nat.cast_zero] at h
      linarith
    · intro hx
      have hCast : (H T x : ℝ) = 0 := by rw [hx] at h; linarith
      exact_mod_cast hCast
  simpa only [hZeroEvent] using hBound


theorem sss_exposure_drift_lemma
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (T : ℕ)
    (hMeas : ∀ s, s ≤ T → Measurable[F s] (Y s))
    (hHalf : ∀ s, s ≤ T → ∀ x, ∃ h : ℕ, Y s x = (h : ℝ) / 2)
    (hInitial : ∀ x, Y 0 x ≤ (T : ℝ) / 8)
    (hGrowth : ∀ s, s < T → ∀ x, Y (s + 1) x ≤ Y s x + 1)
    {q : ℝ} (hq : 0 ≤ q)
    (hDrift : ∀ s, s < T → ∀ᵐ x ∂μ,
      (((T - s) / 16 : ℕ) : ℝ) ≤ Y s x →
      1 - q ≤ (μ[({y | Y (s + 1) y ≤ Y s y - (if 0 < Y s y then (1 / 2 : ℝ) else 0)}).indicator
        (fun _ => (1 : ℝ)) | F s]) x) :
    1 - 4 * q ^ (1 / 8 : ℝ) ≤ μ.real {x | Y T x = 0} := by
  apply half_integer_exposure_process_completion μ F Y T hMeas hHalf hInitial hGrowth hq
  intro s hs
  let B := {x | Y s x - (if 0 < Y s x then (1 / 2 : ℝ) else 0) < Y (s + 1) x}
  have hB : MeasurableSet B := measurableSet_lt
    (((hMeas s (by omega)).mono (F.le s) le_rfl).sub
      (Measurable.ite (measurableSet_lt measurable_const ((hMeas s (by omega)).mono (F.le s) le_rfl))
        measurable_const measurable_const))
    ((hMeas (s + 1) (by omega)).mono (F.le (s + 1)) le_rfl)
  have hGoodEq : {y | Y (s + 1) y ≤ Y s y - (if 0 < Y s y then (1 / 2 : ℝ) else 0)} = Bᶜ := by
    ext x
    simp only [B, Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  have hComplement := conditional_indicator_complement_eq_one_sub μ (F s) (F.le s) hB
  filter_upwards [hDrift s hs, hComplement] with x hx hc hActive
  have hLower := hx hActive
  rw [hGoodEq, hc] at hLower
  linarith

end CircularLaw
