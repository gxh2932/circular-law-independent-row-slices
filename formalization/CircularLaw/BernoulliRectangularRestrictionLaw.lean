import CircularLaw.BernoulliPrincipalMinorLaw
import CircularLaw.BernoulliAdjointLaw
import CircularLaw.BernoulliUniqueRowLaw

/-!
# The exact law of an injective row and column restriction

The rectangular exposure is a coordinate marginal of the actual
ambient entry law. Event probabilities are transferred through this
map, so expansion is proved afresh under the restricted law.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix NNReal

namespace CircularLaw

def bernoulliRectangularRestrictionSample {N M C : ℕ}
    (r : Fin M ↪ Fin N) (c : Fin C ↪ Fin N) (x : BernoulliSquareSample N) :
    Fin M × Fin C → Bool := fun ij => x (r ij.1, c ij.2)

theorem bernoulli_rectangular_restriction_sample_law {N M C : ℕ}
    (r : Fin M ↪ Fin N) (c : Fin C ↪ Fin N) (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).map (bernoulliRectangularRestrictionSample r c) =
      bernoulliCubeLaw (Fin M × Fin C) p hp := by
  let f : Fin M × Fin C ↪ Fin N × Fin N :=
    ⟨fun ij => (r ij.1, c ij.2), by
      intro a b h
      exact Prod.ext (r.injective (congrArg Prod.fst h)) (c.injective (congrArg Prod.snd h))⟩
  exact bernoulli_cube_law_restrict p hp f

theorem bernoulli_rectangular_restriction_measure_preserving {N M C : ℕ}
    (r : Fin M ↪ Fin N) (c : Fin C ↪ Fin N) (p : ℝ≥0) (hp : p ≤ 1) :
    MeasurePreserving (bernoulliRectangularRestrictionSample r c)
      (bernoulliSquareMatrixLaw N p hp) (bernoulliCubeLaw (Fin M × Fin C) p hp) :=
  ⟨measurable_pi_lambda _ (fun ij => measurable_pi_apply (r ij.1, c ij.2)),
    bernoulli_rectangular_restriction_sample_law r c p hp⟩

theorem bernoulli_rectangular_restriction_matrix_eq {N M C : ℕ}
    (r : Fin M ↪ Fin N) (c : Fin C ↪ Fin N) (x : BernoulliSquareSample N) :
    (bernoulliSquareMatrix x).submatrix r c =
      bernoulliRectangularMatrix (bernoulliRectangularRestrictionSample r c x) := rfl

theorem bernoulli_rectangular_restriction_event_probability {N M C : ℕ}
    (r : Fin M ↪ Fin N) (c : Fin C ↪ Fin N) (p : ℝ≥0) (hp : p ≤ 1)
    (E : Matrix (Fin M) (Fin C) ℂ → Prop) :
    (bernoulliSquareMatrixLaw N p hp).real {x | E ((bernoulliSquareMatrix x).submatrix r c)} =
      (bernoulliCubeLaw (Fin M × Fin C) p hp).real {x | E (bernoulliRectangularMatrix x)} := by
  have hEvent : {x : BernoulliSquareSample N | E ((bernoulliSquareMatrix x).submatrix r c)} =
      bernoulliRectangularRestrictionSample r c ⁻¹' {x | E (bernoulliRectangularMatrix x)} := rfl
  rw [hEvent]
  have hMeas : MeasurableSet {x : Fin M × Fin C → Bool | E (bernoulliRectangularMatrix x)} :=
    (Set.to_countable _).measurableSet
  exact congrArg ENNReal.toReal
    ((bernoulli_rectangular_restriction_measure_preserving r c p hp).measure_preimage hMeas.nullMeasurableSet)

theorem bernoulli_adjoint_rectangular_restriction_event_probability {N M C : ℕ}
    (r : Fin M ↪ Fin N) (c : Fin C ↪ Fin N) (p : ℝ≥0) (hp : p ≤ 1)
    (E : Matrix (Fin M) (Fin C) ℂ → Prop) :
    (bernoulliSquareMatrixLaw N p hp).real {x | E ((bernoulliSquareMatrix x)ᴴ.submatrix r c)} =
      (bernoulliCubeLaw (Fin M × Fin C) p hp).real {x | E (bernoulliRectangularMatrix x)} := by
  rw [bernoulli_square_adjoint_event_probability p hp (fun A => E (A.submatrix r c))]
  exact bernoulli_rectangular_restriction_event_probability r c p hp E

end CircularLaw
