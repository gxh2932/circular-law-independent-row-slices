import CircularLaw.IndependentSecondMoment
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProductMeasure

/-!
# The actual independent Bernoulli cube law

The row comparator in Sections 8-9 has independent Bernoulli coordinates.
This law is their product measure, including parameters zero and one.
The centered coordinate has its exact source mean, variance and fourth
moment; independence and marginalization are proved for the actual law.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace CircularLaw

def bernoulliCoordinateLaw (p : ℝ≥0) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p hp).toMeasure

instance bernoulliCoordinateLaw_probability (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernoulliCoordinateLaw p hp) := by
  unfold bernoulliCoordinateLaw
  infer_instance

def bernoulliCenteredValue (p : ℝ≥0) (b : Bool) : ℝ :=
  (cond b 1 0 : ℝ) - p

theorem bernoulliCoordinateLaw_integral (p : ℝ≥0) (hp : p ≤ 1) (f : Bool → ℝ) :
    (∫ b, f b ∂bernoulliCoordinateLaw p hp) = (1 - (p : ℝ)) * f false + p * f true := by
  simp only [bernoulliCoordinateLaw, PMF.integral_eq_sum, Fintype.sum_bool,
    PMF.bernoulli_apply, Bool.cond_false, Bool.cond_true, ENNReal.coe_toReal,
    NNReal.coe_sub hp, NNReal.coe_one, smul_eq_mul]
  ring

theorem bernoulliCenteredValue_mean (p : ℝ≥0) (hp : p ≤ 1) :
    (∫ b, bernoulliCenteredValue p b ∂bernoulliCoordinateLaw p hp) = 0 := by
  rw [bernoulliCoordinateLaw_integral]
  simp only [bernoulliCenteredValue, Bool.cond_false, Bool.cond_true]
  ring

theorem bernoulliCenteredValue_second_moment (p : ℝ≥0) (hp : p ≤ 1) :
    (∫ b, bernoulliCenteredValue p b ^ 2 ∂bernoulliCoordinateLaw p hp) = p * (1 - (p : ℝ)) := by
  rw [bernoulliCoordinateLaw_integral]
  simp only [bernoulliCenteredValue, Bool.cond_false, Bool.cond_true]
  ring

theorem bernoulliCenteredValue_fourth_moment (p : ℝ≥0) (hp : p ≤ 1) :
    (∫ b, bernoulliCenteredValue p b ^ 4 ∂bernoulliCoordinateLaw p hp) =
      p * (1 - (p : ℝ)) * (1 - 3 * (p : ℝ) * (1 - (p : ℝ))) := by
  rw [bernoulliCoordinateLaw_integral]
  simp only [bernoulliCenteredValue, Bool.cond_false, Bool.cond_true]
  ring

theorem bernoulliCenteredValue_fourth_variance_bounds (p : ℝ≥0) (hp : p ≤ 1) :
    0 ≤ (∫ b, bernoulliCenteredValue p b ^ 4 ∂bernoulliCoordinateLaw p hp) -
      (p * (1 - (p : ℝ))) ^ 2 ∧
    (∫ b, bernoulliCenteredValue p b ^ 4 ∂bernoulliCoordinateLaw p hp) -
      (p * (1 - (p : ℝ))) ^ 2 ≤ p * (1 - (p : ℝ)) := by
  rw [bernoulliCenteredValue_fourth_moment]
  have h0 := p.coe_nonneg
  have h1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hσ : 0 ≤ (p : ℝ) * (1 - p) := mul_nonneg h0 (by linarith)
  have hσUpper : (p : ℝ) * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg ((p : ℝ) - 1 / 2)]
  constructor <;> nlinarith [sq_nonneg ((p : ℝ) * (1 - p))]

theorem bernoulli_variance_square_bound (p : ℝ≥0) (hp : p ≤ 1) :
    4 * ((p : ℝ) * (1 - p)) ^ 2 ≤ (p : ℝ) * (1 - p) := by
  have h0 := p.coe_nonneg
  have h1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hσ : 0 ≤ (p : ℝ) * (1 - p) := mul_nonneg h0 (by linarith)
  have hσUpper : (p : ℝ) * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg ((p : ℝ) - 1 / 2)]
  nlinarith

def bernoulliCubeLaw (ι : Type*) [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1) : Measure (ι → Bool) :=
  Measure.pi (fun _ : ι => bernoulliCoordinateLaw p hp)

instance bernoulliCubeLaw_probability (ι : Type*) [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernoulliCubeLaw ι p hp) := by
  unfold bernoulliCubeLaw
  infer_instance

theorem bernoulliCubeLaw_memLp {ι : Type*} [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (f : (ι → Bool) → ℝ) (q : ℝ≥0∞) : MemLp f q (bernoulliCubeLaw ι p hp) := by
  exact ⟨(measurable_of_countable f).aestronglyMeasurable, eLpNorm_lt_top_of_finite⟩

theorem bernoulliCubeLaw_coordinate_integral {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (i : ι) (f : Bool → ℝ) :
    (∫ x : ι → Bool, f (x i) ∂bernoulliCubeLaw ι p hp) =
      ∫ b, f b ∂bernoulliCoordinateLaw p hp := by
  rw [← integral_map (μ := bernoulliCubeLaw ι p hp) (φ := fun x => x i)
    (measurable_pi_apply i).aemeasurable (measurable_of_countable f).aestronglyMeasurable]
  rw [bernoulliCubeLaw, (measurePreserving_eval (fun _ : ι => bernoulliCoordinateLaw p hp) i).map_eq]

theorem bernoulliCubeLaw_coordinate_independent {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) :
    iIndepFun (fun i : ι => fun x : ι → Bool => bernoulliCenteredValue p (x i))
      (bernoulliCubeLaw ι p hp) :=
  iIndepFun_pi (fun _ => (measurable_of_countable (bernoulliCenteredValue p)).aemeasurable)

theorem bernoulliCubeLaw_centered_coordinate_mean {ι : Type*} [Fintype ι]
    (p : ℝ≥0) (hp : p ≤ 1) (i : ι) :
    (∫ x : ι → Bool, bernoulliCenteredValue p (x i) ∂bernoulliCubeLaw ι p hp) = 0 := by
  rw [bernoulliCubeLaw_coordinate_integral, bernoulliCenteredValue_mean]

theorem bernoulliCubeLaw_centered_coordinate_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ≥0) (hp : p ≤ 1) (i j : ι) :
    (∫ x : ι → Bool, bernoulliCenteredValue p (x i) * bernoulliCenteredValue p (x j)
      ∂bernoulliCubeLaw ι p hp) = if i = j then p * (1 - (p : ℝ)) else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [← pow_two]
    change (∫ x : ι → Bool, bernoulliCenteredValue p (x i) ^ 2 ∂bernoulliCubeLaw ι p hp) =
      p * (1 - (p : ℝ))
    rw [bernoulliCubeLaw_coordinate_integral p hp i (fun b => bernoulliCenteredValue p b ^ 2),
      bernoulliCenteredValue_second_moment]
  · rw [if_neg hij]
    have hInd := (bernoulliCubeLaw_coordinate_independent p hp).indepFun hij
    have hMoment := hInd.integral_fun_mul_eq_mul_integral
      (bernoulliCubeLaw_memLp p hp _ 2).aestronglyMeasurable
      (bernoulliCubeLaw_memLp p hp _ 2).aestronglyMeasurable
    simpa only [Pi.mul_apply, bernoulliCubeLaw_centered_coordinate_mean, mul_zero] using hMoment

end CircularLaw
