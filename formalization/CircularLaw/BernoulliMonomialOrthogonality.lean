import CircularLaw.RegularizedDistanceMean

/-!
# Orthogonality of the source Bernoulli quadratic monomials

Independence is applied to the actual product law, including functions
of a repeated coordinate. Centered squares are orthogonal across distinct
coordinates and to off-diagonal products. Off-diagonal products have
nonzero covariance only for the same unordered pair.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace CircularLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bernoulliCenteredSquare (p : ℝ≥0) (b : Bool) : ℝ :=
  bernoulliCenteredValue p b ^ 2 - p * (1 - (p : ℝ))

theorem bernoulliCenteredSquare_mean (p : ℝ≥0) (hp : p ≤ 1) :
    (∫ b, bernoulliCenteredSquare p b ∂bernoulliCoordinateLaw p hp) = 0 := by
  simp only [bernoulliCenteredSquare]
  rw [integral_sub Integrable.of_finite Integrable.of_finite, bernoulliCenteredValue_second_moment]
  simp only [integral_const, probReal_univ, one_smul, sub_self]

theorem bernoulliCenteredSquare_second_moment (p : ℝ≥0) (hp : p ≤ 1) :
    (∫ b, bernoulliCenteredSquare p b ^ 2 ∂bernoulliCoordinateLaw p hp) =
      p * (1 - (p : ℝ)) * (1 - 4 * (p : ℝ) * (1 - (p : ℝ))) := by
  rw [bernoulliCoordinateLaw_integral]
  simp only [bernoulliCenteredSquare, bernoulliCenteredValue, Bool.cond_false, Bool.cond_true]
  ring

omit [DecidableEq ι] in
theorem bernoulliCubeLaw_transformed_pair (p : ℝ≥0) (hp : p ≤ 1)
    (i j : ι) (hij : i ≠ j) (f g : Bool → ℝ) :
    (∫ x, f (x i) * g (x j) ∂bernoulliCubeLaw ι p hp) =
      (∫ b, f b ∂bernoulliCoordinateLaw p hp) * (∫ b, g b ∂bernoulliCoordinateLaw p hp) := by
  have hInd : iIndepFun (fun k : ι => fun x : ι → Bool => x k) (bernoulliCubeLaw ι p hp) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hPair := (hInd.indepFun hij).comp (measurable_of_countable f) (measurable_of_countable g)
  have hIntegral := hPair.integral_fun_mul_eq_mul_integral
    (bernoulliCubeLaw_memLp p hp _ 2).aestronglyMeasurable
    (bernoulliCubeLaw_memLp p hp _ 2).aestronglyMeasurable
  simpa only [Function.comp_apply, bernoulliCubeLaw_coordinate_integral] using hIntegral

theorem bernoulliCubeLaw_square_covariance (p : ℝ≥0) (hp : p ≤ 1) (i j : ι) :
    (∫ x, bernoulliCenteredSquare p (x i) * bernoulliCenteredSquare p (x j)
      ∂bernoulliCubeLaw ι p hp) =
      if i = j then p * (1 - (p : ℝ)) * (1 - 4 * (p : ℝ) * (1 - (p : ℝ))) else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    simp only [← pow_two]
    rw [bernoulliCubeLaw_coordinate_integral p hp i (fun b => bernoulliCenteredSquare p b ^ 2),
      bernoulliCenteredSquare_second_moment]
  · rw [if_neg hij, bernoulliCubeLaw_transformed_pair p hp i j hij,
      bernoulliCenteredSquare_mean, zero_mul]

omit [DecidableEq ι] in
theorem bernoulliCubeLaw_pair_square_moment (p : ℝ≥0) (hp : p ≤ 1)
    (i j : ι) (hij : i ≠ j) :
    (∫ x, bernoulliCenteredValue p (x i) ^ 2 * bernoulliCenteredValue p (x j) ^ 2
      ∂bernoulliCubeLaw ι p hp) = (p * (1 - (p : ℝ))) ^ 2 := by
  rw [bernoulliCubeLaw_transformed_pair p hp i j hij
    (fun b => bernoulliCenteredValue p b ^ 2) (fun b => bernoulliCenteredValue p b ^ 2),
    bernoulliCenteredValue_second_moment, pow_two]

omit [DecidableEq ι] in
theorem bernoulliCubeLaw_three_singleton_zero (p : ℝ≥0) (hp : p ≤ 1)
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f (bernoulliCenteredValue p (x i), bernoulliCenteredValue p (x j)) *
      bernoulliCenteredValue p (x k) ∂bernoulliCubeLaw ι p hp) = 0 := by
  have hPair := (bernoulliCubeLaw_coordinate_independent p hp).indepFun_prodMk
    (fun _ => measurable_of_countable _) i j k hik hjk
  have hInd := hPair.comp hf measurable_id
  have hIntegral := hInd.integral_fun_mul_eq_mul_integral
    (bernoulliCubeLaw_memLp p hp _ 2).aestronglyMeasurable
    (bernoulliCubeLaw_memLp p hp _ 2).aestronglyMeasurable
  simpa only [Function.comp_apply, id_eq, bernoulliCubeLaw_centered_coordinate_mean,
    mul_zero] using hIntegral

omit [DecidableEq ι] in
theorem bernoulliCubeLaw_square_pair_orthogonal (p : ℝ≥0) (hp : p ≤ 1)
    (i j k : ι) (hjk : j ≠ k) :
    (∫ x, bernoulliCenteredSquare p (x i) *
      (bernoulliCenteredValue p (x j) * bernoulliCenteredValue p (x k))
      ∂bernoulliCubeLaw ι p hp) = 0 := by
  by_cases hij : i = j
  · subst j
    have h := bernoulliCubeLaw_three_singleton_zero p hp i i k hjk hjk
      (fun z => (z.1 ^ 2 - p * (1 - (p : ℝ))) * z.2) (by fun_prop)
    simpa only [bernoulliCenteredSquare, mul_assoc] using h
  · have h := bernoulliCubeLaw_three_singleton_zero p hp i k j hij hjk.symm
      (fun z => (z.1 ^ 2 - p * (1 - (p : ℝ))) * z.2) (by fun_prop)
    convert h using 1
    congr with x
    simp only [bernoulliCenteredSquare]
    ring

theorem bernoulliCubeLaw_disjoint_pair_orthogonal (p : ℝ≥0) (hp : p ≤ 1)
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hij : i ≠ j) :
    (∫ x, (bernoulliCenteredValue p (x i) * bernoulliCenteredValue p (x j)) *
      (bernoulliCenteredValue p (x k) * bernoulliCenteredValue p (x l))
      ∂bernoulliCubeLaw ι p hp) = 0 := by
  have hPairs := (bernoulliCubeLaw_coordinate_independent p hp).indepFun_prodMk_prodMk
    (fun _ => measurable_of_countable _) i j k l hik hil hjk hjl
  have hInd := hPairs.comp (φ := fun z : ℝ × ℝ => z.1 * z.2)
    (ψ := fun z : ℝ × ℝ => z.1 * z.2) (by fun_prop) (by fun_prop)
  have hIntegral := hInd.integral_fun_mul_eq_mul_integral
    (bernoulliCubeLaw_memLp p hp _ 2).aestronglyMeasurable
    (bernoulliCubeLaw_memLp p hp _ 2).aestronglyMeasurable
  simpa only [Function.comp_apply, bernoulliCubeLaw_centered_coordinate_product,
    if_neg hij, zero_mul] using hIntegral

theorem bernoulliCubeLaw_pair_covariance (p : ℝ≥0) (hp : p ≤ 1)
    (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l) :
    (∫ x, (bernoulliCenteredValue p (x i) * bernoulliCenteredValue p (x j)) *
      (bernoulliCenteredValue p (x k) * bernoulliCenteredValue p (x l))
      ∂bernoulliCubeLaw ι p hp) =
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then (p * (1 - (p : ℝ))) ^ 2 else 0 := by
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      rw [if_pos (Or.inl ⟨rfl, rfl⟩)]
      convert bernoulliCubeLaw_pair_square_moment p hp i j hij using 1
      congr with x
      ring
    · have hMismatch : ¬ ((i = i ∧ j = l) ∨ (i = l ∧ j = i)) := by aesop
      rw [if_neg hMismatch]
      have h := bernoulliCubeLaw_three_singleton_zero p hp i j l hkl hjl
        (fun z => z.1 ^ 2 * z.2) (by fun_prop)
      convert h using 1
      congr with x
      ring
  · by_cases hil : i = l
    · subst l
      by_cases hjk : j = k
      · subst k
        rw [if_pos (Or.inr ⟨rfl, rfl⟩)]
        convert bernoulliCubeLaw_pair_square_moment p hp i j hij using 1
        congr with x
        ring
      · have hMismatch : ¬ ((i = k ∧ j = i) ∨ (i = i ∧ j = k)) := by aesop
        rw [if_neg hMismatch]
        have h := bernoulliCubeLaw_three_singleton_zero p hp i j k hik hjk
          (fun z => z.1 ^ 2 * z.2) (by fun_prop)
        convert h using 1
        congr with x
        ring
    · by_cases hjk : j = k
      · subst k
        have hMismatch : ¬ ((i = j ∧ j = l) ∨ (i = l ∧ j = j)) := by aesop
        rw [if_neg hMismatch]
        have h := bernoulliCubeLaw_three_singleton_zero p hp i j l hil hkl
          (fun z => z.1 * z.2 ^ 2) (by fun_prop)
        convert h using 1
        congr with x
        ring
      · by_cases hjl : j = l
        · subst l
          have hMismatch : ¬ ((i = k ∧ j = j) ∨ (i = j ∧ j = k)) := by aesop
          rw [if_neg hMismatch]
          have h := bernoulliCubeLaw_three_singleton_zero p hp i j k hik hjk
            (fun z => z.1 * z.2 ^ 2) (by fun_prop)
          convert h using 1
          congr with x
          ring
        · have hMismatch : ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) := by aesop
          rw [if_neg hMismatch]
          exact bernoulliCubeLaw_disjoint_pair_orthogonal p hp i j k l hik hil hjk hjl hij

end CircularLaw
