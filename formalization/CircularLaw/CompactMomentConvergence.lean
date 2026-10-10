import CircularLaw.CompactMomentExistence
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# From actual moment limits and an upper-bound event to weak convergence

Weierstrass approximation gives a polynomial for each continuous test on
the compact interval. Its empirical mean has the proved probability
limit. Outside the upper-bound failure event, the approximation controls
the empirical mean and its limiting integral, proving the full test limit.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Topology

namespace CircularLaw

theorem compact_probability_polynomial_integral {R : ℝ}
    (ν : ProbabilityMeasure (Set.Icc (0 : ℝ) R)) (a : ℕ → ℝ)
    (hMom : ∀ m, (∫ t, (t : ℝ) ^ m ∂(ν : Measure (Set.Icc (0 : ℝ) R))) = a m)
    (p : Polynomial ℝ) :
    (∫ t, p.eval (t : ℝ) ∂(ν : Measure (Set.Icc (0 : ℝ) R))) = polynomialMomentValue a p := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, polynomialMomentValue]
  rw [integral_finset_sum]
  · simp only [integral_const_mul, hMom]
  · intro k _
    exact (continuous_const.mul (continuous_subtype_val.pow k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem finiteMean_pointwise_error {α : Type*} [Fintype α] [Nonempty α]
    {f g : α → ℝ} {ε : ℝ} (h : ∀ j, |f j - g j| ≤ ε) :
    |finiteMean f - finiteMean g| ≤ ε := by
  rw [← finiteMean_sub]
  exact (abs_finiteMean_le _).trans ((finiteMean_mono h).trans_eq (finiteMean_const ε))

theorem varying_probability_continuous_of_compact_moments {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → Fin n → ℝ)
    (a : ℕ → ℝ) (R : ℝ) (hNonneg : ∀ n x j, 0 ≤ s n x j)
    (hBad : Tendsto (fun n => (μ n).real {x | ∃ j, R < s n x j}) atTop (𝓝 0))
    (hMom : ∀ m, VaryingConvergesInProbability μ
      (fun n x => finiteMean (fun j => s n x j ^ m)) (a m))
    (ν : ProbabilityMeasure (Set.Icc (0 : ℝ) R))
    (hν : ∀ m, (∫ t, (t : ℝ) ^ m ∂(ν : Measure (Set.Icc (0 : ℝ) R))) = a m)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) R)) :
    VaryingConvergesInProbability μ (fun n x => finiteMean (fun j => f (s n x j)))
      (∫ t, f (t : ℝ) ∂(ν : Measure (Set.Icc (0 : ℝ) R))) := by
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 R f hf (ε / 4) (by positivity)
  have hpInt : Integrable (fun t : Set.Icc (0 : ℝ) R => p.eval (t : ℝ)) (ν : Measure (Set.Icc (0 : ℝ) R)) :=
    (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfInt : Integrable (fun t : Set.Icc (0 : ℝ) R => f (t : ℝ)) (ν : Measure (Set.Icc (0 : ℝ) R)) :=
    (continuousOn_iff_continuous_restrict.mp hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntegral : |polynomialMomentValue a p - ∫ t, f (t : ℝ) ∂(ν : Measure (Set.Icc (0 : ℝ) R))| ≤ ε / 4 := by
    rw [← compact_probability_polynomial_integral ν a hν p, ← integral_sub hpInt hfInt]
    have h := norm_integral_le_of_norm_le_const (μ := (ν : Measure (Set.Icc (0 : ℝ) R)))
      (f := fun t => p.eval (t : ℝ) - f (t : ℝ))
      (ae_of_all (ν : Measure (Set.Icc (0 : ℝ) R)) (fun t => by
        rw [Real.norm_eq_abs]
        exact (hp t t.property).le))
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h
  have hPoly := varying_probability_polynomial_mean μ s a hMom p
  have hSum := hBad.add (hPoly (ε / 2) (by positivity))
  simp only [add_zero] at hSum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall (fun _ => measureReal_nonneg))
  filter_upwards [eventually_gt_atTop 0] with n hn
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply (measureReal_mono (μ := μ n) (s₂ :=
    {x | ∃ j, R < s n x j} ∪
      {x | ε / 2 < |finiteMean (fun j => p.eval (s n x j)) - polynomialMomentValue a p|}) ?_
    (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  intro x hx
  by_contra h
  have hNot := not_or.mp h
  have hBound (j : Fin n) : s n x j ∈ Set.Icc (0 : ℝ) R :=
    ⟨hNonneg _ _ _, le_of_not_gt (fun hj => hNot.1 ⟨j, hj⟩)⟩
  have hApprox : |finiteMean (fun j => f (s n x j)) -
      finiteMean (fun j => p.eval (s n x j))| ≤ ε / 4 :=
    finiteMean_pointwise_error (fun j => by rw [abs_sub_comm]; exact (hp _ (hBound j)).le)
  have hP : |finiteMean (fun j => p.eval (s n x j)) - polynomialMomentValue a p| ≤ ε / 2 :=
    le_of_not_gt hNot.2
  have hTriangle := abs_sub_le (finiteMean (fun j => f (s n x j)))
    (finiteMean (fun j => p.eval (s n x j)))
    (∫ t, f (t : ℝ) ∂(ν : Measure (Set.Icc (0 : ℝ) R)))
  have hTriangleP := abs_sub_le (finiteMean (fun j => p.eval (s n x j)))
    (polynomialMomentValue a p) (∫ t, f (t : ℝ) ∂(ν : Measure (Set.Icc (0 : ℝ) R)))
  change ε < |finiteMean (fun j => f (s n x j)) - ∫ t, f (t : ℝ) ∂(ν : Measure (Set.Icc (0 : ℝ) R))| at hx
  linarith

end CircularLaw
