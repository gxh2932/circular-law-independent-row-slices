import CircularLaw.SourceKernelBridge
import CircularLaw.UniformSteepNetExclusion

/-!
# The source kernel event and its probability assembly

Failure of the deterministic kernel alternative is contained in the
three actual shifted-class kernel events or row-load failure. All four
checked exponents imply the source inverse-dimension bound with a fixed
absolute logarithmic lower constant.
-/

noncomputable section
open Classical

namespace CircularLaw

def SourceKernelCompatible {n d : ℕ} (L : ℕ) (a a₃ : ℝ)
    (I : Finset (Fin n)) (ζ : ℂ) (rows : RowSliceMatrix n d) : Prop :=
  {x | x ≠ 0 ∧ (retainedShiftedMatrix I ζ rows).mulVec x = 0} ⊆
    sourceVL n L a ∪ nonzeroScalarCone (sourceGradual n d L a₃)

theorem source_kernel_failure_union_bound {n d L : ℕ} {a a₃ : ℝ}
    (I : Finset (Fin n)) (ζ : ℂ)
    (hAlternative : ∀ rows : RowSliceMatrix n d, SourceRowLoad I (thirdSteepScale n a₃) rows →
      (∀ x ∈ sourceShiftedT0 n d L, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0) →
      (∀ x ∈ sourceShiftedT1 n d L, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0) →
      (∀ x ∈ sourceShiftedT2 n d L a₃, (retainedShiftedMatrix I ζ rows).mulVec x ≠ 0) →
        SourceKernelCompatible L a a₃ I ζ rows) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceKernelCompatible L a a₃ I ζ rows) ≤
      uniformProbability (fun rows : RowSliceMatrix n d =>
        ∃ v ∈ sourceShiftedT0 n d L, (retainedShiftedMatrix I ζ rows).mulVec v = 0) +
      uniformProbability (fun rows : RowSliceMatrix n d =>
        ∃ v ∈ sourceShiftedT1 n d L, (retainedShiftedMatrix I ζ rows).mulVec v = 0) +
      uniformProbability (fun rows : RowSliceMatrix n d =>
        ∃ v ∈ sourceShiftedT2 n d L a₃, (retainedShiftedMatrix I ζ rows).mulVec v = 0) +
      uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceRowLoad I (thirdSteepScale n a₃) rows) := by
  let E₀ := fun rows : RowSliceMatrix n d => ∃ v ∈ sourceShiftedT0 n d L,
    (retainedShiftedMatrix I ζ rows).mulVec v = 0
  let E₁ := fun rows : RowSliceMatrix n d => ∃ v ∈ sourceShiftedT1 n d L,
    (retainedShiftedMatrix I ζ rows).mulVec v = 0
  let E₂ := fun rows : RowSliceMatrix n d => ∃ v ∈ sourceShiftedT2 n d L a₃,
    (retainedShiftedMatrix I ζ rows).mulVec v = 0
  let ELoad := fun rows : RowSliceMatrix n d => ¬SourceRowLoad I (thirdSteepScale n a₃) rows
  have hEvent : ∀ rows : RowSliceMatrix n d, ¬SourceKernelCompatible L a a₃ I ζ rows →
      E₀ rows ∨ E₁ rows ∨ E₂ rows ∨ ELoad rows := by
    intro rows hBad
    by_cases h₀ : E₀ rows
    · exact Or.inl h₀
    by_cases h₁ : E₁ rows
    · exact Or.inr (Or.inl h₁)
    by_cases h₂ : E₂ rows
    · exact Or.inr (Or.inr (Or.inl h₂))
    by_cases hLoad : ELoad rows
    · exact Or.inr (Or.inr (Or.inr hLoad))
    apply False.elim
    apply hBad
    apply hAlternative rows (by simpa only [ELoad, not_not] using hLoad)
    · intro x hx hKernel
      exact h₀ ⟨x, hx, hKernel⟩
    · intro x hx hKernel
      exact h₁ ⟨x, hx, hKernel⟩
    · intro x hx hKernel
      exact h₂ ⟨x, hx, hKernel⟩
  apply (uniformProbability_mono hEvent).trans
  calc
    _ ≤ uniformProbability E₀ + uniformProbability (fun rows => E₁ rows ∨ E₂ rows ∨ ELoad rows) :=
      uniformProbability_or_le _ _
    _ ≤ uniformProbability E₀ + (uniformProbability E₁ +
        (uniformProbability E₂ + uniformProbability ELoad)) := by
      apply add_le_add (le_refl _)
      exact (uniformProbability_or_le _ _).trans
        (add_le_add (le_refl _) (uniformProbability_or_le _ _))
    _ = _ := by ring

theorem uniformProbability_not {α : Type*} [Fintype α] [Nonempty α] (E : α → Prop) :
    uniformProbability (fun x => ¬E x) = 1 - uniformProbability E := by
  have hPoint : (fun x : α => (if E x then (1 : ℝ) else 0) + (if ¬E x then (1 : ℝ) else 0)) =
      (fun _ : α => (1 : ℝ)) := by
    funext x
    by_cases h : E x <;> simp only [h, not_true_eq_false, not_false_eq_true, if_true, if_false] <;> norm_num
  have h := congrArg finiteMean hPoint
  rw [finiteMean_add, finiteMean_indicator, finiteMean_indicator, finiteMean_const] at h
  linarith

def sourceKernelFailureRate : ℝ :=
  min (5 * uniqueWitnessRate / 2)
    (min (sourceT1KernelRate (1 / 4)) (min (sourceT2KernelRate (1 / 4)) (rowLoadRate / 4)))

def sourceKernelLowerConstant : ℝ := 1 / (4 * sourceKernelFailureRate)

theorem sourceKernelFailureRate_pos : 0 < sourceKernelFailureRate := by
  unfold sourceKernelFailureRate
  exact lt_min (by positivity [uniqueWitnessRate_pos])
    (lt_min (sourceT1KernelRate_pos (by norm_num))
      (lt_min (sourceT2KernelRate_pos (by norm_num)) (div_pos rowLoadRate_pos (by norm_num))))

theorem sourceKernelLowerConstant_pos : 0 < sourceKernelLowerConstant := by
  exact div_pos zero_lt_one (mul_pos (by norm_num) sourceKernelFailureRate_pos)

theorem source_kernel_log_failure_scale {n d : ℕ} {C : ℝ}
    (h : SourceKernelConditions n d) (hC : sourceKernelLowerConstant ≤ C)
    (hLower : C * Real.log (n : ℝ) ≤ (d : ℝ)) :
    Real.log (n : ℝ) ≤ sourceKernelFailureRate * n / (d : ℝ) ^ 3 := by
  have hDimension := source_kernel_dimension_twice_degree h
  have hdR : (0 : ℝ) < d := by exact_mod_cast hDimension.2.1
  have hNOne : (1 : ℝ) ≤ n := by exact_mod_cast hDimension.1
  have hLog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hNOne
  have hRate := sourceKernelFailureRate_pos
  have hCoefficient : 1 ≤ 4 * sourceKernelFailureRate * C := by
    have h := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hRate)).mp hC
    change 1 ≤ C * (4 * sourceKernelFailureRate) at h
    nlinarith
  have hDensity : 4 * (d : ℝ) ≤ (n : ℝ) / (d : ℝ) ^ 3 := by
    apply (le_div_iff₀ (pow_pos hdR 3)).mpr
    have hReal : 4 * (d : ℝ) ^ 4 ≤ n := by exact_mod_cast h.dimension_fourth
    convert hReal using 1
    ring
  calc
    _ ≤ (4 * sourceKernelFailureRate * C) * Real.log (n : ℝ) := by
      have hScaled := mul_le_mul_of_nonneg_right hCoefficient hLog
      simpa only [one_mul] using hScaled
    _ = (4 * sourceKernelFailureRate) * (C * Real.log (n : ℝ)) := by ring
    _ ≤ (4 * sourceKernelFailureRate) * d := mul_le_mul_of_nonneg_left hLower (by positivity)
    _ = sourceKernelFailureRate * (4 * (d : ℝ)) := by ring
    _ ≤ sourceKernelFailureRate * ((n : ℝ) / (d : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hDensity hRate.le
    _ = _ := by ring

theorem degree_sqrt_le_cube {d : ℕ} (hd : 0 < d) : Real.sqrt d ≤ (d : ℝ) ^ 3 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hRoot : Real.sqrt d ≤ (d : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg (d : ℝ)) (Nat.cast_nonneg d)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg d)]
    nlinarith
  have hPower := Nat.pow_le_pow_right hd (by decide : 1 ≤ 3)
  simp only [pow_one] at hPower
  exact hRoot.trans (by exact_mod_cast hPower)

theorem exp_negative_le_inverse_dimension {n : ℕ} {q : ℝ} (hn : 0 < n)
    (hLog : Real.log (n : ℝ) ≤ q) : Real.exp (-q) ≤ 1 / (n : ℝ) := by
  calc
    _ ≤ Real.exp (-Real.log (n : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hn : (0 : ℝ) < n), one_div]

theorem source_kernel_four_rates_le_inverse_dimension {n d : ℕ} {C : ℝ}
    (h : SourceKernelConditions n d) (hC : sourceKernelLowerConstant ≤ C)
    (hLower : C * Real.log (n : ℝ) ≤ (d : ℝ)) :
    Real.exp (-(5 * uniqueWitnessRate / 2) * n / (d : ℝ) ^ 3) +
      Real.exp (-sourceT1KernelRate (1 / 4) * n / Real.sqrt d) +
      Real.exp (-sourceT2KernelRate (1 / 4) * n) +
      Real.exp (-(rowLoadRate / 4) * n) ≤ 4 / (n : ℝ) := by
  have hDimension := source_kernel_dimension_twice_degree h
  have hn := hDimension.1
  have hd := hDimension.2.1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hRoot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hLog := source_kernel_log_failure_scale h hC hLower
  rw [mul_div_assoc] at hLog
  have hRate₀ : sourceKernelFailureRate ≤ 5 * uniqueWitnessRate / 2 := min_le_left _ _
  have hRate₁ : sourceKernelFailureRate ≤ sourceT1KernelRate (1 / 4) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hRate₂ : sourceKernelFailureRate ≤ sourceT2KernelRate (1 / 4) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRateLoad : sourceKernelFailureRate ≤ rowLoadRate / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hRatioRoot : (n : ℝ) / (d : ℝ) ^ 3 ≤ (n : ℝ) / Real.sqrt d :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg n) hRoot (degree_sqrt_le_cube hd)
  have hCubeOne : (1 : ℝ) ≤ (d : ℝ) ^ 3 := by
    have hCubePos : 0 < d ^ 3 := pow_pos hd 3
    exact_mod_cast (by omega : 1 ≤ d ^ 3)
  have hRatioN : (n : ℝ) / (d : ℝ) ^ 3 ≤ n := div_le_self (Nat.cast_nonneg n) hCubeOne
  have h₀ := exp_negative_le_inverse_dimension hn
    (hLog.trans (mul_le_mul_of_nonneg_right hRate₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) / (d : ℝ) ^ 3)))
  have h₁ := exp_negative_le_inverse_dimension hn
    (hLog.trans ((mul_le_mul_of_nonneg_left hRatioRoot sourceKernelFailureRate_pos.le).trans
      (mul_le_mul_of_nonneg_right hRate₁ (by positivity : (0 : ℝ) ≤ (n : ℝ) / Real.sqrt d))))
  have h₂ := exp_negative_le_inverse_dimension hn
    (hLog.trans ((mul_le_mul_of_nonneg_left hRatioN sourceKernelFailureRate_pos.le).trans
      (mul_le_mul_of_nonneg_right hRate₂ (Nat.cast_nonneg n : (0 : ℝ) ≤ n))))
  have hLoad := exp_negative_le_inverse_dimension hn
    (hLog.trans ((mul_le_mul_of_nonneg_left hRatioN sourceKernelFailureRate_pos.le).trans
      (mul_le_mul_of_nonneg_right hRateLoad (Nat.cast_nonneg n : (0 : ℝ) ≤ n))))
  simp only [neg_mul, neg_div, mul_div_assoc] at h₀ h₁ h₂ hLoad ⊢
  calc
    _ ≤ 1 / (n : ℝ) + 1 / n + 1 / n + 1 / n :=
      add_le_add (add_le_add (add_le_add h₀ h₁) h₂) hLoad
    _ = _ := by ring

end CircularLaw
