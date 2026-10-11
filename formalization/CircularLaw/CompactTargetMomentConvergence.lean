import CircularLaw.PolynomialMomentTailApproximation

/-!
# Weak convergence to a compact target from actual empirical moments

The samples need only be nonnegative, with every empirical moment
converging in probability to the compact target's moment. Approximate a
bounded continuous test on an interval larger than the target support.
A higher moment controls the polynomial's error outside that interval;
the compact target bound makes its limiting tail as small as needed.
The argument permits exceptional large singular values in every sample.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Topology

namespace CircularLaw

theorem varying_probability_bounded_continuous_of_indexed_compact_target_moments {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (q : ℕ → ℕ) (hPositive : ∀ᶠ n in atTop, 0 < q n)
    (s : ∀ n, Ω n → Fin (q n) → ℝ)
    (a : ℕ → ℝ) (R : ℝ) (hR : 0 ≤ R) (hNonneg : ∀ n x j, 0 ≤ s n x j)
    (hMom : ∀ m, VaryingConvergesInProbability μ
      (fun n x => finiteMean (fun j => s n x j ^ m)) (a m))
    (ν : ProbabilityMeasure (Set.Icc (0 : ℝ) R))
    (hν : ∀ m, (∫ t, (t : ℝ) ^ m ∂(ν : Measure (Set.Icc (0 : ℝ) R))) = a m)
    (f : ℝ → ℝ) (hf : Continuous f) (hBound : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    VaryingConvergesInProbability μ (fun n x => finiteMean (fun j => f (s n x j)))
      (∫ t, f (t : ℝ) ∂(ν : Measure (Set.Icc (0 : ℝ) R))) := by
  intro ε hε
  obtain ⟨M, hM⟩ := hBound
  let S := R + 1
  have hS : 1 ≤ S := by dsimp [S]; linarith
  have hSPos : 0 < S := by linarith
  have hRS : R < S := by dsimp [S]; linarith
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 S f hf.continuousOn
    (ε / 4) (by positivity)
  let C := |M| + polynomialAbsoluteCoefficientSum p + 1
  have hC : 0 < C := by
    dsimp [C]
    nlinarith [abs_nonneg M, polynomial_absolute_coefficient_sum_nonneg p]
  obtain ⟨k, hk⟩ := high_moment_tail_coefficient_exists (C := C) hR hSPos hRS
    (by positivity : 0 < ε / 8) p.natDegree
  let K := C / S ^ k
  have hK : 0 < K := div_pos hC (pow_pos hSPos k)
  let δ := ε / (8 * K)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hKδ : K * δ = ε / 8 := by
    dsimp [δ]
    field_simp
  have hTargetTail : K * a (p.natDegree + k) < ε / 8 := by
    apply lt_of_le_of_lt _ hk
    exact mul_le_mul_of_nonneg_left
      (by rw [← hν]; exact compact_probability_moment_upper_bound ν _) hK.le
  have hpInt : Integrable (fun t : Set.Icc (0 : ℝ) R => p.eval (t : ℝ))
      (ν : Measure (Set.Icc (0 : ℝ) R)) :=
    (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfInt : Integrable (fun t : Set.Icc (0 : ℝ) R => f (t : ℝ))
      (ν : Measure (Set.Icc (0 : ℝ) R)) :=
    (hf.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntegral : |polynomialMomentValue a p -
      ∫ t, f (t : ℝ) ∂(ν : Measure (Set.Icc (0 : ℝ) R))| ≤ ε / 4 := by
    rw [← compact_probability_polynomial_integral ν a hν p, ← integral_sub hpInt hfInt]
    have h := norm_integral_le_of_norm_le_const (μ := (ν : Measure (Set.Icc (0 : ℝ) R)))
      (f := fun t => p.eval (t : ℝ) - f (t : ℝ))
      (ae_of_all (ν : Measure (Set.Icc (0 : ℝ) R)) (fun t => by
        rw [Real.norm_eq_abs]
        exact (hp t ⟨t.property.1, t.property.2.trans hRS.le⟩).le))
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h
  have hPoly := varying_probability_polynomial_mean μ s a hMom p
  have hSum := (hMom (p.natDegree + k) δ hδ).add (hPoly (ε / 4) (by positivity))
  simp only [add_zero] at hSum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [hPositive] with n hn
  letI : Nonempty (Fin (q n)) := ⟨⟨0, hn⟩⟩
  apply (measureReal_mono (μ := μ n) (s₂ :=
    {x | δ < |finiteMean (fun j => s n x j ^ (p.natDegree + k)) - a (p.natDegree + k)|} ∪
      {x | ε / 4 < |finiteMean (fun j => p.eval (s n x j)) - polynomialMomentValue a p|}) ?_
    (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  intro x hx
  by_contra h
  have hNot := not_or.mp h
  have hHigh : finiteMean (fun j => s n x j ^ (p.natDegree + k)) ≤ a (p.natDegree + k) + δ := by
    have hAbs : |finiteMean (fun j => s n x j ^ (p.natDegree + k)) - a (p.natDegree + k)| ≤ δ :=
      le_of_not_gt hNot.1
    have hLe := (abs_le.mp hAbs).2
    linarith
  have hTail : K * finiteMean (fun j => s n x j ^ (p.natDegree + k)) ≤ ε / 4 := by
    have h := mul_le_mul_of_nonneg_left hHigh hK.le
    rw [mul_add, hKδ] at h
    linarith
  have hApprox : |finiteMean (fun j => f (s n x j)) -
      finiteMean (fun j => p.eval (s n x j))| ≤ ε / 2 := by
    have hA := polynomial_high_moment_finite_mean_error p f M S (ε / 4) hM hS
      (by positivity) (fun t ht => (hp t ht).le) k (s n x) (hNonneg n x)
    change _ ≤ ε / 4 + K * finiteMean (fun j => s n x j ^ (p.natDegree + k)) at hA
    linarith
  have hP : |finiteMean (fun j => p.eval (s n x j)) - polynomialMomentValue a p| ≤ ε / 4 :=
    le_of_not_gt hNot.2
  have hTriangle := abs_sub_le (finiteMean (fun j => f (s n x j)))
    (finiteMean (fun j => p.eval (s n x j)))
    (∫ t, f (t : ℝ) ∂(ν : Measure (Set.Icc (0 : ℝ) R)))
  have hTriangleP := abs_sub_le (finiteMean (fun j => p.eval (s n x j)))
    (polynomialMomentValue a p) (∫ t, f (t : ℝ) ∂(ν : Measure (Set.Icc (0 : ℝ) R)))
  change ε < |finiteMean (fun j => f (s n x j)) -
    ∫ t, f (t : ℝ) ∂(ν : Measure (Set.Icc (0 : ℝ) R))| at hx
  linarith

theorem varying_probability_bounded_continuous_of_compact_target_moments {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ)
    (a : ℕ → ℝ) (R : ℝ) (hR : 0 ≤ R) (hNonneg : ∀ n x j, 0 ≤ s n x j)
    (hMom : ∀ m, VaryingConvergesInProbability μ
      (fun n x => finiteMean (fun j => s n x j ^ m)) (a m))
    (ν : ProbabilityMeasure (Set.Icc (0 : ℝ) R))
    (hν : ∀ m, (∫ t, (t : ℝ) ^ m ∂(ν : Measure (Set.Icc (0 : ℝ) R))) = a m)
    (f : ℝ → ℝ) (hf : Continuous f) (hBound : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    VaryingConvergesInProbability μ (fun n x => finiteMean (fun j => f (s n x j)))
      (∫ t, f (t : ℝ) ∂(ν : Measure (Set.Icc (0 : ℝ) R))) :=
  varying_probability_bounded_continuous_of_indexed_compact_target_moments μ id
    (eventually_gt_atTop 0) s a R hR hNonneg hMom ν hν f hf hBound

end CircularLaw
