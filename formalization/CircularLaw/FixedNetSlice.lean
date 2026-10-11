import CircularLaw.CanonicalProfileStatistics
import CircularLaw.ProfileTensorization
import CircularLaw.SteepNetCardinalityFinite

/-!
# The fixed gradual-net row-slice probability estimate

The weight range follows from the actual canonical heights and the
logarithmic lower bound. Slice conditioning is applied to the same
rectangular matrix event, with every deterministic vector translation.
The final radius is exactly `R*log(d)*sqrt(d*n)/k`.
-/

noncomputable section
open Classical Filter
open scoped Topology

namespace CircularLaw

def orderedProfileSliceEstimate {n : ℕ} (k d K : ℕ) (y : Fin n → ℂ) (τ : ℝ) : ℝ :=
  let P := orderedCanonicalRowProfile y ((d : ℝ) / k)
  Real.exp (2 * (K : ℝ) * (d : ℝ) ^ 2 / n) *
    (4 * Real.exp 1 * rowSmallBallConstant * τ ^ 2 *
      (4 * Real.exp (-averagedProfileRate * profileCoordinateDispersion P d) *
        profileGeometricMean P.part (truncatedProfileWeight P d) +
          Real.exp (-averagedProfileRate * Real.rpow (d : ℝ) (2 / 3)))) ^ K

def fixedNetSliceEstimate {n : ℕ} (k d K : ℕ) (y : Fin n → ℂ) (R : ℝ) : ℝ :=
  let P := orderedCanonicalRowProfile y ((d : ℝ) / k)
  Real.exp (2 * (K : ℝ) * (d : ℝ) ^ 2 / n) *
    (4 * Real.exp 1 * rowSmallBallConstant * R ^ 2 * ((n : ℝ) / K) * Real.log d ^ 2 *
      (4 * Real.exp (-averagedProfileRate * profileCoordinateDispersion P d) *
        profileGeometricMean P.part (truncatedProfileWeight P d) +
          Real.exp (-averagedProfileRate * Real.rpow (d : ℝ) (2 / 3)))) ^ K

theorem ordered_canonical_profile_slice_estimate {n k d K : ℕ}
    (hn : 0 < n) (hd : 65536 ≤ d) (hdn : 2 * d ≤ n) (hk : 0 < k)
    (hLogN : 2 ≤ Real.log n) (hLower : 96 * Real.log n ≤ (d : ℝ))
    (hDegree : Real.rpow (d : ℝ) (1 / 3) *
      Real.exp (-binomialHalfRate * Real.rpow (d : ℝ) (2 / 3)) ≤
        Real.exp (-(binomialHalfRate / 2) * Real.rpow (d : ℝ) (2 / 3)))
    (y : Fin n → ℂ) (hy : IsKVector k y) {τ : ℝ} (hτ : 1 ≤ τ) (V : Fin K → ℂ) :
    uniformProbability (fun rows : Fin K → RowSlice n d =>
      matrixVectorL2Norm (sliceRectangularMatrix rows) y V ≤
        τ * Real.sqrt ((d : ℝ) * K) / k) ≤ orderedProfileSliceEstimate k d K y τ := by
  let η := (d : ℝ) / k
  have hdPos : 0 < d := by omega
  have hRange (a b : Fin n) :
      |dyadicWeight (truncatedProfileWeight (canonicalRowProfile y η) d
          ((canonicalRowProfile y η).part a)) -
        dyadicWeight (truncatedProfileWeight (canonicalRowProfile y η) d
          ((canonicalRowProfile y η).part b))| ≤ (d : ℝ) / 12 := by
    have h := truncated_profile_range_le_degree hn hdPos (by omega) hLogN hLower
      (orderedCanonicalRowProfile y η) (orderedCanonicalRowProfile_height_le y η) a b
    simpa only [orderedCanonical_coordinate_weight_eq] using h
  have h := canonical_profile_slice_tensorization hn hd hdn hk y hy hRange hDegree hτ V
  change _ ≤ Real.exp (2 * (K : ℝ) * (d : ℝ) ^ 2 / n) *
    (4 * Real.exp 1 * rowSmallBallConstant * τ ^ 2 *
      (4 * Real.exp (-averagedProfileRate * profileCoordinateDispersion (canonicalRowProfile y η) d) *
        profileGeometricMean (canonicalRowProfile y η).part
          (truncatedProfileWeight (canonicalRowProfile y η) d) +
            Real.exp (-averagedProfileRate * Real.rpow (d : ℝ) (2 / 3)))) ^ K at h
  rw [← orderedCanonical_profile_dispersion_eq y η d, ← orderedCanonical_profile_mean_eq y η hdPos] at h
  exact h

theorem fixed_net_slice_estimate {n k d K : ℕ}
    (hn : 0 < n) (hd : 65536 ≤ d) (hdn : 2 * d ≤ n) (hk : 0 < k)
    (hLogN : 2 ≤ Real.log n) (hLower : 96 * Real.log n ≤ (d : ℝ)) (hLogD : 1 ≤ Real.log d)
    (hDegree : Real.rpow (d : ℝ) (1 / 3) *
      Real.exp (-binomialHalfRate * Real.rpow (d : ℝ) (2 / 3)) ≤
        Real.exp (-(binomialHalfRate / 2) * Real.rpow (d : ℝ) (2 / 3)))
    (hK : 0 < K) (hKn : K ≤ n) (y : Fin n → ℂ) (hy : IsKVector k y)
    {R : ℝ} (hR : 1 ≤ R) (V : Fin K → ℂ) :
    uniformProbability (fun rows : Fin K → RowSlice n d =>
      matrixVectorL2Norm (sliceRectangularMatrix rows) y V ≤
        R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤ fixedNetSliceEstimate k d K y R := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hNK : 1 ≤ (n : ℝ) / K := (le_div_iff₀ hKR).mpr (by
    rw [one_mul]
    exact_mod_cast hKn)
  have hDiv : 0 ≤ (n : ℝ) / K := div_nonneg (Nat.cast_nonneg n) hKR.le
  have hSqrt : 1 ≤ Real.sqrt ((n : ℝ) / K) :=
    (Real.le_sqrt (by norm_num) hDiv).mpr (by simpa only [one_pow] using hNK)
  let τ := R * Real.log d * Real.sqrt ((n : ℝ) / K)
  have hFirst : 1 ≤ R * Real.log d := by
    simpa only [one_mul] using mul_le_mul hR hLogD (by norm_num) (by linarith : 0 ≤ R)
  have hτ : 1 ≤ τ := by
    simpa only [one_mul] using mul_le_mul hFirst hSqrt (by norm_num)
      (by linarith : 0 ≤ R * Real.log d)
  have hRootProduct : Real.sqrt ((n : ℝ) / K) * Real.sqrt ((d : ℝ) * K) =
      Real.sqrt ((d : ℝ) * n) := by
    rw [← Real.sqrt_mul hDiv]
    congr 1
    field_simp
  have hRadius : τ * Real.sqrt ((d : ℝ) * K) / k =
      R * Real.log d * Real.sqrt ((d : ℝ) * n) / k := by
    dsimp only [τ]
    rw [mul_assoc, hRootProduct]
  have hτSq : τ ^ 2 = R ^ 2 * Real.log d ^ 2 * ((n : ℝ) / K) := by
    dsimp only [τ]
    rw [mul_pow, mul_pow, Real.sq_sqrt hDiv]
  have h := ordered_canonical_profile_slice_estimate hn hd hdn hk hLogN hLower hDegree y hy hτ V
  rw [hRadius] at h
  apply h.trans_eq
  dsimp only [orderedProfileSliceEstimate, fixedNetSliceEstimate]
  rw [hτSq]
  congr 2
  ring

theorem eventually_fixed_net_slice_estimate_uniform {Clower : ℝ} (hC : 96 ≤ Clower) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand Clower σ n d →
      ∀ k : ℕ, 0 < k → ∀ K : ℕ, 0 < K → K ≤ n →
        ∀ y : Fin n → ℂ, IsKVector k y → ∀ R : ℝ, 1 ≤ R → ∀ V : Fin K → ℂ,
          uniformProbability (fun rows : Fin K → RowSlice n d =>
            matrixVectorL2Norm (sliceRectangularMatrix rows) y V ≤
              R * Real.log d * Real.sqrt ((d : ℝ) * n) / k) ≤ fixedNetSliceEstimate k d K y R := by
  have hCPos : 0 < Clower := by linarith
  have hCast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hLogN := (Real.tendsto_log_atTop.comp hCast).eventually_ge_atTop 2
  have hLogD := (Real.tendsto_log_atTop.comp hCast).eventually_ge_atTop 1
  filter_upwards [eventually_source_kernel_conditions_uniform hCPos (1 + σ),
    eventually_degree_property_uniform hCPos
      ((eventually_ge_atTop 65536).and (eventually_profile_prefactor_absorbed.and hLogD)), hLogN]
    with n hConditions hDegree hLogN
  intro d hBand k hk K hK hKn y hy R hR V
  have hFinite := source_kernel_dimension_twice_degree (hConditions d hBand.1 hBand.2)
  obtain ⟨hd, hPrefactor, hLogD⟩ := hDegree d hBand.1
  change 2 ≤ Real.log (n : ℝ) at hLogN
  change 1 ≤ Real.log (d : ℝ) at hLogD
  have hLower : 96 * Real.log n ≤ (d : ℝ) :=
    (mul_le_mul_of_nonneg_right hC (by linarith : 0 ≤ Real.log n)).trans hBand.1
  exact fixed_net_slice_estimate hFinite.1 hd hFinite.2.2 hk hLogN hLower hLogD
    hPrefactor hK hKn y hy hR V

end CircularLaw
