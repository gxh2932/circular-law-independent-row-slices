import CircularLaw.CanonicalProfile
import CircularLaw.ProfileRange
import CircularLaw.ProfileConditioning

/-!
# Row estimates for constructed canonical profiles

The regular block estimate is transported to the exact profile fiber, so
conditioning gives the regular inverse-weight bound for the actual row
sum. The averaged estimator is also specialized to the ordered canonical
profile, discharging its height hypothesis from the construction.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def canonicalRegularFiberEquiv {n : ℕ} (y : Fin n → ℂ) (δ : ℝ)
    (q : CanonicalLabel y δ) (hq : q.val.1 = false) :
    {i : Fin n // (canonicalRowProfile y δ).part i = q} ≃
      {i : Fin n // i ∈ regularPart y q.val.2.val δ} :=
  Equiv.subtypeEquivRight (fun i => by
    simpa only [taggedPart, taggedValues, hq, Bool.false_eq_true, ↓reduceIte, regularPart] using
      canonicalCoordinateLabel_eq_iff y δ i q)

theorem canonical_regular_profile_block_small_ball {n k m d : ℕ} (hk : 0 < k)
    (hm : 1 ≤ m) (hmd : m ≤ d) (y : Fin n → ℂ) (hy : IsKVector k y)
    (q : CanonicalLabel y ((d : ℝ) / (k : ℝ))) (hq : q.val.1 = false)
    {τ : ℝ} (hτ : 1 ≤ τ) (z : ℂ) :
    uniformProbability (fun x : Fin m →
      {i : Fin n // (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part i = q} =>
        ‖(∑ a, y (x a).val) - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) ≤
      40000 * τ ^ 2 * (((canonicalRowProfile y ((d : ℝ) / (k : ℝ))).height q : ℝ) *
        ((m : ℝ) / (d : ℝ)))⁻¹ := by
  let δ := (d : ℝ) / (k : ℝ)
  let e := Equiv.piCongrRight (fun _ : Fin m => canonicalRegularFiberEquiv y δ q hq)
  have hReindex := uniformProbability_reindex e (fun x =>
    ‖(∑ a : Fin m, y (x a).val) - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ))
  change uniformProbability (fun x : Fin m →
    {i : Fin n // (canonicalRowProfile y δ).part i = q} =>
      ‖(∑ a, y (x a).val) - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) = _ at hReindex
  rw [hReindex]
  have hPart : (regularPart y q.val.2.val δ).Nonempty := by
    simpa only [taggedPart, taggedValues, hq, Bool.false_eq_true, ↓reduceIte, regularPart] using
      q.property
  have hBound := canonical_regular_part_small_ball hk hm hmd y hy q.val.2.val hτ hPart z
  simpa only [canonicalRowProfile, taggedValues, hq, Bool.false_eq_true, ↓reduceIte,
    ] using hBound

theorem canonical_conditional_regular_small_ball {n k d : ℕ} (hk : 0 < k)
    (y : Fin n → ℂ) (hy : IsKVector k y) (reference : Fin d → Fin n)
    (q : CanonicalLabel y ((d : ℝ) / (k : ℝ))) (hq : q.val.1 = false)
    (hm : 1 ≤ profileCounts (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part reference q)
    {τ : ℝ} (hτ : 1 ≤ τ) (z : ℂ) :
    uniformProbability (fun samples : ProfileFiber
      (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part d
      (profileCounts (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part reference) =>
        ‖(∑ i, y (samples.val i)) - z‖ ≤ τ * Real.sqrt (d : ℝ) / (k : ℝ)) ≤
      40000 * τ ^ 2 * (actualProfileWeight
        (canonicalRowProfile y ((d : ℝ) / (k : ℝ))) reference q)⁻¹ := by
  have hmd := trialCount_le_degree (fun i =>
    (canonicalRowProfile y ((d : ℝ) / (k : ℝ))).part i = q) reference
  apply conditional_profile_sum_le_block _ ⟨⟨reference, rfl⟩⟩ y q
  intro w
  have h := canonical_regular_profile_block_small_ball hk hm hmd y hy q hq hτ w
  simpa only [actualProfileWeight, canonicalRowProfile, hq, Bool.false_eq_true,
    ↓reduceIte, mul_div_assoc, profileCounts] using h

theorem eventually_canonical_profile_estimator {C : ℝ} {d : ℕ → ℕ}
    (hC : 96 ≤ C) (hlog : LogLowerBound C d) (hsparse : SparseDegrees d) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ hd : 2 ≤ d n, ∀ y : Fin n → ℂ, ∀ δ : ℝ,
      let P := orderedCanonicalRowProfile y δ
      finiteMean (fun samples : Fin (d n) → Fin n =>
        profileEstimator P.part (actualProfileWeight P samples) (by omega) samples) ≤
        4 * Real.exp (-averagedProfileRate *
          pairDispersion (fun a => dyadicWeight (truncatedProfileWeight P (d n) (P.part a)))) *
            profileGeometricMean P.part (truncatedProfileWeight P (d n)) +
              Real.exp (-averagedProfileRate * Real.rpow (d n : ℝ) (2 / 3 : ℝ)) := by
  filter_upwards [eventually_averaged_profile_estimator hC hlog hsparse] with n hn
  intro hd y δ
  exact hn hd _ (orderedCanonicalRowProfile y δ) (orderedCanonicalRowProfile_height_le y δ)

end CircularLaw
