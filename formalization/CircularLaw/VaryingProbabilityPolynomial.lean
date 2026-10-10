import CircularLaw.VaryingProbabilitySqueeze
import CircularLaw.FiniteMean
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Finite polynomial tests from moment convergence in probability

Every polynomial empirical mean is the exact finite linear combination of
the empirical moments. Addition and deterministic scaling preserve the
actual probability limits on varying sample spaces.
-/

noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators Topology

namespace CircularLaw

theorem varying_probability_const {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (a : ℝ) :
    VaryingConvergesInProbability μ (fun _ _ => a) a := by
  intro ε hε
  simpa only [sub_self, abs_zero, not_lt_of_ge hε.le, Set.setOf_false, measureReal_empty] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem varying_probability_add {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    {f g : ∀ n, Ω n → ℝ} {a b : ℝ}
    (hf : VaryingConvergesInProbability μ f a) (hg : VaryingConvergesInProbability μ g b) :
    VaryingConvergesInProbability μ (fun n x => f n x + g n x) (a + b) := by
  simpa only [sub_neg_eq_add] using varying_probability_sub μ hf (varying_probability_neg μ hg)

theorem varying_probability_finset_sum {Ω : ℕ → Type*} {ι : Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : Finset ι)
    (f : ι → ∀ n, Ω n → ℝ) (a : ι → ℝ)
    (hf : ∀ i ∈ s, VaryingConvergesInProbability μ (f i) (a i)) :
    VaryingConvergesInProbability μ (fun n x => ∑ i ∈ s, f i n x) (∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using varying_probability_const μ 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact varying_probability_add μ (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem finiteMean_finset_sum {α ι : Type*} [Fintype α]
    (s : Finset ι) (f : ι → α → ℝ) :
    finiteMean (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, finiteMean (f i) := by
  simp only [finiteMean, ← Finset.sum_div]
  rw [Finset.sum_comm]

def polynomialMomentValue (a : ℕ → ℝ) (p : Polynomial ℝ) : ℝ :=
  ∑ k ∈ p.support, p.coeff k * a k

theorem empirical_polynomial_mean {α : Type*} [Fintype α] (s : α → ℝ) (p : Polynomial ℝ) :
    finiteMean (fun j => p.eval (s j)) =
      ∑ k ∈ p.support, p.coeff k * finiteMean (fun j => s j ^ k) := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, finiteMean_finset_sum, finiteMean_const_mul]

theorem varying_probability_polynomial_mean {Ω ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (s : ∀ n, Ω n → ι n → ℝ)
    (a : ℕ → ℝ)
    (hMom : ∀ k, VaryingConvergesInProbability μ
      (fun n x => finiteMean (fun j => s n x j ^ k)) (a k)) (p : Polynomial ℝ) :
    VaryingConvergesInProbability μ
      (fun n x => finiteMean (fun j => p.eval (s n x j))) (polynomialMomentValue a p) := by
  simp only [empirical_polynomial_mean, polynomialMomentValue]
  apply varying_probability_finset_sum
  intro k _
  exact varying_probability_mul_deterministic μ (hMom k) tendsto_const_nhds

end CircularLaw
