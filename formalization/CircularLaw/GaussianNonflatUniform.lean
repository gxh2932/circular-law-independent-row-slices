import CircularLaw.GaussianNonflatNet
import CircularLaw.LogarithmicNetCost

/-!
# Uniform non-flatness for all unit Gaussian combinations

The explicit sphere grid has polynomial resolution. When the normal
dimension is at least sqrt(n) and the copy count is at most n^(1/4),
its logarithmic cardinality is eventually absorbed by the small-ball
exponent. This closes the source non-flatness estimate with an explicit
absolute constant and actual unit coefficient quantifiers.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory Filter
open scoped BigOperators Topology

namespace CircularLaw

theorem gaussianNonflat_copy_count_le_dimension {n p : ℕ} (hn : 1 ≤ n)
    (hp : (p : ℝ) ≤ Real.rpow (n : ℝ) (1 / 4)) : p ≤ n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hPower : Real.rpow (n : ℝ) (1 / 4) ≤ n := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (1 / 4 : ℝ) ≤ 1)
  exact_mod_cast hp.trans hPower

theorem gaussianNonflat_grid_log_bound {n p : ℕ} (hn : 1 ≤ n) (hp : p ≤ n) :
    Real.log (2 * (gaussianNonflatGridResolution n p : ℝ) + 3) ≤
      Real.log 8195 + 4 * Real.log (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpR : (p : ℝ) ≤ n := by exact_mod_cast hp
  have hSq : (p : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg p) (by linarith)).mpr hpR
  have hMul := mul_le_mul_of_nonneg_right hSq (sq_nonneg (n : ℝ))
  have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hnR
  have hBase : 2 * (gaussianNonflatGridResolution n p : ℝ) + 3 ≤ 8195 * (n : ℝ) ^ 4 := by
    simp only [gaussianNonflatGridResolution, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    nlinarith
  have hnPos : (0 : ℝ) < n := by linarith
  apply (Real.log_le_log (by positivity) hBase).trans_eq
  rw [Real.log_mul (by norm_num : (8195 : ℝ) ≠ 0) (pow_ne_zero 4 hnPos.ne'), Real.log_pow]
  simp

theorem gaussianNonflat_grid_entropy_bound {n p m : ℕ} (hn : 1 ≤ n)
    (hp : (p : ℝ) ≤ Real.rpow (n : ℝ) (1 / 4)) (hm : Real.sqrt n ≤ (m : ℝ))
    (hLog : Real.log 8195 + 4 * Real.log (n : ℝ) ≤
      (1 / 2048 : ℝ) * Real.rpow (n : ℝ) (1 / 4)) :
    (2 * (p : ℝ)) * Real.log (2 * (gaussianNonflatGridResolution n p : ℝ) + 3) ≤
      (m : ℝ) / 1024 := by
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpNat := gaussianNonflat_copy_count_le_dimension hn hp
  have hLogBound := (gaussianNonflat_grid_log_bound hn hpNat).trans hLog
  have hBaseOne : (1 : ℝ) ≤ 2 * (gaussianNonflatGridResolution n p : ℝ) + 3 := by
    linarith [(Nat.cast_nonneg (gaussianNonflatGridResolution n p) :
      (0 : ℝ) ≤ gaussianNonflatGridResolution n p)]
  have hLogNonneg := Real.log_nonneg hBaseOne
  have hPowerSq : Real.rpow (n : ℝ) (1 / 4) * Real.rpow (n : ℝ) (1 / 4) = Real.sqrt n := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hnPos, show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow]
  calc
    _ ≤ (2 * Real.rpow (n : ℝ) (1 / 4)) *
        ((1 / 2048 : ℝ) * Real.rpow (n : ℝ) (1 / 4)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) hLogBound
        hLogNonneg (mul_nonneg (by norm_num) (Real.rpow_pos_of_pos hnPos _).le)
    _ = Real.sqrt n / 1024 := by nlinarith [hPowerSq]
    _ ≤ _ := div_le_div_of_nonneg_right hm (by norm_num)

theorem gaussianNonflat_grid_smallBall_decay {n p m : ℕ} (hn : 1 ≤ n)
    (hp : (p : ℝ) ≤ Real.rpow (n : ℝ) (1 / 4)) (hm : Real.sqrt n ≤ (m : ℝ))
    (hLog : Real.log 8195 + 4 * Real.log (n : ℝ) ≤
      (1 / 2048 : ℝ) * Real.rpow (n : ℝ) (1 / 4)) :
    (2 * (gaussianNonflatGridResolution n p : ℝ) + 3) ^ (2 * p) *
      Real.exp (-(m : ℝ) / 512) ≤ Real.exp (-(m : ℝ) / 1024) := by
  have hEntropy := gaussianNonflat_grid_entropy_bound hn hp hm hLog
  have hBase : (0 : ℝ) < 2 * (gaussianNonflatGridResolution n p : ℝ) + 3 := by positivity
  have hPower : (2 * (gaussianNonflatGridResolution n p : ℝ) + 3) ^ (2 * p) =
      Real.exp ((2 * (p : ℝ)) * Real.log (2 * (gaussianNonflatGridResolution n p : ℝ) + 3)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.exp_log hBase] using
      (Real.exp_nat_mul (Real.log (2 * (gaussianNonflatGridResolution n p : ℝ) + 3)) (2 * p)).symm
  rw [hPower, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

theorem gaussianNonflat_coordinate_error_decay {n p m : ℕ}
    (hn : 3 ≤ n) (hp : p ≤ n) (hm : m ≤ n) :
    (p : ℝ) * n * Real.exp (-(n : ℝ) ^ 2) ≤ Real.exp (-(m : ℝ) / 1024) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpR : (p : ℝ) ≤ n := by exact_mod_cast hp
  have hmR : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hnExp : (n : ℝ) ≤ Real.exp (n : ℝ) := by linarith [Real.add_one_le_exp (n : ℝ)]
  have hCount : (p : ℝ) * n ≤ Real.exp (2 * (n : ℝ)) := by
    calc
      _ ≤ (n : ℝ) ^ 2 := by nlinarith
      _ ≤ Real.exp (n : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hnExp 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ Real.exp (2 * (n : ℝ)) * Real.exp (-(n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hCount (Real.exp_pos _).le
    _ = Real.exp (2 * (n : ℝ) - (n : ℝ) ^ 2) := by rw [← Real.exp_add]; rfl
    _ ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])

theorem gaussianNonflat_two_failures_decay {m : ℕ} (hm : 2048 ≤ m) :
    Real.exp (-(m : ℝ) / 1024) + Real.exp (-(m : ℝ) / 1024) ≤
      Real.exp (-(m : ℝ) / 2048) := by
  have hmR : (2048 : ℝ) ≤ m := by exact_mod_cast hm
  have hTwo : (2 : ℝ) ≤ Real.exp ((m : ℝ) / 2048) := by
    apply (by linarith [Real.add_one_le_exp 1] : (2 : ℝ) ≤ Real.exp 1).trans
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ = 2 * Real.exp (-(m : ℝ) / 1024) := by ring
    _ ≤ Real.exp ((m : ℝ) / 2048) * Real.exp (-(m : ℝ) / 1024) :=
      mul_le_mul_of_nonneg_right hTwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem projectedGaussianCopies_uniform_nonflat_exponential {n p m : ℕ}
    (hn : 3 ≤ n) (hp : 0 < p) (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (hm : m ≤ Module.finrank ℂ Eᗮ) (hLarge : 2048 ≤ m)
    (hNormal : Real.sqrt n ≤ (m : ℝ))
    (hCopies : (p : ℝ) ≤ Real.rpow (n : ℝ) (1 / 4))
    (hLog : Real.log 8195 + 4 * Real.log (n : ℝ) ≤
      (1 / 2048 : ℝ) * Real.rpow (n : ℝ) (1 / 4)) :
    (standardGaussianCopiesLaw n p).real
      {z | ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
        orderedNormAt (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i)
          (m / 2048) ≤ (m : ℝ) / (2048 * n)} ≤ Real.exp (-(m : ℝ) / 2048) := by
  have hnPos : 0 < n := by omega
  have hmn : m ≤ n := hm.trans (by simpa using Eᗮ.finrank_le)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hSubset : {z | ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
      orderedNormAt (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i)
        (m / 2048) ≤ (m : ℝ) / (2048 * n)} ⊆
      {z | ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
        orderedNormAt (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i)
          (m / 512) ≤ (m : ℝ) / (1024 * n)} := by
    rintro z ⟨x, hx, hSmall⟩
    refine ⟨x, hx, ?_⟩
    apply (orderedNormAt_antitone _ (by omega : 0 < m / 2048)
      (by omega : m / 2048 ≤ m / 512) (by omega : m / 512 ≤ n)).trans
    exact hSmall.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith))
  apply ((measureReal_mono hSubset).trans
    (projectedGaussianCopies_uniform_nonflat_grid_bound hnPos hp E hm (by omega))).trans
  apply (add_le_add
    (gaussianNonflat_coordinate_error_decay hn
      (gaussianNonflat_copy_count_le_dimension (by omega) hCopies) hmn)
    (gaussianNonflat_grid_smallBall_decay (by omega) hCopies hNormal hLog)).trans
  exact gaussianNonflat_two_failures_decay hLarge

theorem eventually_projectedGaussianCopies_uniform_nonflat :
    ∀ᶠ n : ℕ in atTop, ∀ (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (m p : ℕ),
      m ≤ Module.finrank ℂ Eᗮ → Real.sqrt n ≤ (m : ℝ) → 0 < p →
      (p : ℝ) ≤ Real.rpow (n : ℝ) (1 / 4) →
      (standardGaussianCopiesLaw n p).real
        {z | ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
          orderedNormAt (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i)
            (m / 2048) ≤ (m : ℝ) / (2048 * n)} ≤ Real.exp (-(m : ℝ) / 2048) := by
  filter_upwards [eventually_ge_atTop (2048 ^ 2),
    eventually_log_power_degree_budget (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1 / 2048) (Real.log 8195) 4 (by norm_num)]
      with n hn hLog
  intro E m p hm hNormal hp hCopies
  have hnR : (2048 : ℝ) ^ 2 ≤ n := by exact_mod_cast hn
  have hSqrt := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hSqrtNonneg := Real.sqrt_nonneg (n : ℝ)
  have hmLargeR : (2048 : ℝ) ≤ m := by nlinarith
  have hmLarge : 2048 ≤ m := by exact_mod_cast hmLargeR
  exact projectedGaussianCopies_uniform_nonflat_exponential (by omega) hp E hm hmLarge
    hNormal hCopies hLog

theorem gaussianCopiesCombination_nonzero_of_positive_order {n p : ℕ}
    (Y : Fin p → EuclideanSpace ℂ (Fin n)) (x : EuclideanSpace ℂ (Fin p)) (r : ℕ)
    (hLower : 0 < orderedNormAt (fun i => gaussianCopiesCombination Y x i) r) :
    gaussianCopiesCombination Y x ≠ 0 := by
  intro hZero
  simp [hZero, orderedNormAt, orderedNorm] at hLower

theorem projectedGaussianCopies_uniform_nonflat_success_of_bound {n p m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (E : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (hBound : (standardGaussianCopiesLaw n p).real
      {z | ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
        orderedNormAt (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i)
          (m / 2048) ≤ (m : ℝ) / (2048 * n)} ≤ Real.exp (-(m : ℝ) / 2048)) :
    ∃ A : Set (Fin p → (Fin n → ℂ)), MeasurableSet A ∧
      1 - Real.exp (-(m : ℝ) / 2048) ≤ (standardGaussianCopiesLaw n p).real A ∧
      ∀ z ∈ A, ∀ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 →
        (m : ℝ) / (2048 * n) < orderedNormAt
          (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i) (m / 2048) ∧
        gaussianCopiesCombination (projectedGaussianCopies E z) x ≠ 0 := by
  let B := {z | ∃ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 ∧
    orderedNormAt (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i)
      (m / 2048) ≤ (m : ℝ) / (2048 * n)}
  have hB : MeasurableSet B := projectedGaussianCopies_uniform_nonflat_measurableSet E _ _
  have hτ : (0 : ℝ) < (m : ℝ) / (2048 * n) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  refine ⟨Bᶜ, hB.compl, ?_, ?_⟩
  · rw [probReal_compl_eq_one_sub hB]
    exact sub_le_sub_left hBound 1
  · intro z hz x hx
    have hOrder : (m : ℝ) / (2048 * n) < orderedNormAt
        (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i) (m / 2048) :=
      lt_of_not_ge (fun h => hz ⟨x, hx, h⟩)
    exact ⟨hOrder, gaussianCopiesCombination_nonzero_of_positive_order _ _ _ (hτ.trans hOrder)⟩

theorem eventually_projectedGaussianCopies_uniform_nonflat_success :
    ∀ᶠ n : ℕ in atTop, ∀ (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (m p : ℕ),
      m ≤ Module.finrank ℂ Eᗮ → Real.sqrt n ≤ (m : ℝ) → 0 < p →
      (p : ℝ) ≤ Real.rpow (n : ℝ) (1 / 4) →
      ∃ A : Set (Fin p → (Fin n → ℂ)), MeasurableSet A ∧
        1 - Real.exp (-(m : ℝ) / 2048) ≤ (standardGaussianCopiesLaw n p).real A ∧
        ∀ z ∈ A, ∀ x : EuclideanSpace ℂ (Fin p), ‖x‖ = 1 →
          (m : ℝ) / (2048 * n) < orderedNormAt
            (fun i => gaussianCopiesCombination (projectedGaussianCopies E z) x i) (m / 2048) ∧
          gaussianCopiesCombination (projectedGaussianCopies E z) x ≠ 0 := by
  filter_upwards [eventually_projectedGaussianCopies_uniform_nonflat, eventually_ge_atTop 1]
    with n hBound hn
  intro E m p hm hNormal hp hCopies
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hmR : (0 : ℝ) < m := (Real.sqrt_pos.mpr hnR).trans_le hNormal
  have hmPos : 0 < m := by exact_mod_cast hmR
  exact projectedGaussianCopies_uniform_nonflat_success_of_bound hnPos hmPos E
    (hBound E m p hm hNormal hp hCopies)

end CircularLaw
