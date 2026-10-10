import CircularLaw.ComplexGaussianRotation
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Exact products of independent Gaussian entries

The product law has the actual standard complex Gaussian marginal at
every finite coordinate. Arbitrary words, including repeated indices,
are grouped by multiplicity. Their expectations vanish unless every
entry occurs equally often with and without conjugation, and otherwise
equal the product of the multiplicity factorials.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CircularLaw

def standardComplexGaussianProductLaw (ι : Type*) [Fintype ι] : Measure (ι → ℂ) :=
  Measure.pi (fun _ => standardComplexGaussianLaw)

instance standardComplexGaussianProductLaw_probability (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (standardComplexGaussianProductLaw ι) := by
  unfold standardComplexGaussianProductLaw
  infer_instance

theorem gaussian_product_law_coordinate {ι : Type*} [Fintype ι] (i : ι) :
    (standardComplexGaussianProductLaw ι).map (fun x => x i) = standardComplexGaussianLaw :=
  (measurePreserving_eval (fun _ : ι => standardComplexGaussianLaw) i).map_eq

theorem gaussian_product_law_independent (ι : Type*) [Fintype ι] :
    iIndepFun (fun i (x : ι → ℂ) => x i) (standardComplexGaussianProductLaw ι) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)

theorem gaussian_entry_monomial_integrable {ι : Type*} [Fintype ι] (p q : ι → ℕ) :
    Integrable (fun x : ι → ℂ => ∏ i, x i ^ p i * star (x i) ^ q i)
      (standardComplexGaussianProductLaw ι) :=
  Integrable.fintype_prod (fun i => standard_complex_gaussian_mixed_power_integrable (p i) (q i))

theorem gaussian_entry_monomial_integral {ι : Type*} [Fintype ι] (p q : ι → ℕ) :
    (∫ x : ι → ℂ, ∏ i, x i ^ p i * star (x i) ^ q i
      ∂standardComplexGaussianProductLaw ι) =
      if ∀ i, p i = q i then (∏ i, (p i).factorial : ℂ) else 0 := by
  rw [standardComplexGaussianProductLaw,
    integral_fintype_prod_eq_prod (fun i (z : ℂ) => z ^ p i * star z ^ q i)]
  simp only [standard_complex_gaussian_mixed_moment]
  by_cases h : ∀ i, p i = q i
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i _
    rw [if_pos (h i)]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

def gaussianEntryWord {ι : Type*} (u v : List ι) (x : ι → ℂ) : ℂ :=
  (u.map x).prod * (v.map (fun i => star (x i))).prod

theorem finite_word_product_eq_count_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : List ι) (f : ι → ℂ) :
    (u.map f).prod = ∏ i, f i ^ u.count i := by
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [List.count_eq_zero_of_not_mem (by simpa only [List.mem_toFinset] using hi), pow_zero]

theorem gaussian_entry_word_eq_count_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : List ι) (x : ι → ℂ) :
    gaussianEntryWord u v x = ∏ i, x i ^ u.count i * star (x i) ^ v.count i := by
  rw [gaussianEntryWord, finite_word_product_eq_count_product,
    finite_word_product_eq_count_product, Finset.prod_mul_distrib]

theorem gaussian_entry_word_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : List ι) : Integrable (gaussianEntryWord u v) (standardComplexGaussianProductLaw ι) := by
  have hWord : gaussianEntryWord u v =
      fun x => ∏ i, x i ^ u.count i * star (x i) ^ v.count i :=
    funext (gaussian_entry_word_eq_count_product u v)
  rw [hWord]
  exact gaussian_entry_monomial_integrable _ _

theorem gaussian_entry_word_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : List ι) :
    (∫ x : ι → ℂ, gaussianEntryWord u v x ∂standardComplexGaussianProductLaw ι) =
      if ∀ i, u.count i = v.count i then (∏ i, (u.count i).factorial : ℂ) else 0 := by
  simp only [gaussian_entry_word_eq_count_product]
  exact gaussian_entry_monomial_integral _ _

theorem gaussian_entry_word_unbalanced_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : List ι) (i : ι) (hi : u.count i ≠ v.count i) :
    (∫ x : ι → ℂ, gaussianEntryWord u v x ∂standardComplexGaussianProductLaw ι) = 0 := by
  rw [gaussian_entry_word_integral, if_neg (fun h => hi (h i))]

theorem finite_word_counts_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (u : List ι) :
    (∑ i, u.count i) = u.length := by
  calc
    _ = ∑ i ∈ u.toFinset, u.count i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      exact List.count_eq_zero_of_not_mem (by simpa only [List.mem_toFinset] using hi)
    _ = _ := List.sum_toFinset_count_eq_length u

theorem gaussian_entry_word_length_mismatch_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : List ι) (hLength : u.length ≠ v.length) :
    (∫ x : ι → ℂ, gaussianEntryWord u v x ∂standardComplexGaussianProductLaw ι) = 0 := by
  rw [gaussian_entry_word_integral]
  apply if_neg
  intro h
  have hSum := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h i)
  rw [finite_word_counts_sum, finite_word_counts_sum] at hSum
  exact hLength hSum

theorem gaussian_entry_word_integral_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : List ι) :
    ‖∫ x : ι → ℂ, gaussianEntryWord u v x ∂standardComplexGaussianProductLaw ι‖ ≤
      (u.length.factorial : ℝ) := by
  rw [gaussian_entry_word_integral]
  split_ifs
  · have hDiv := Nat.prod_factorial_dvd_factorial_sum Finset.univ (fun i => u.count i)
    rw [finite_word_counts_sum] at hDiv
    have hLe := Nat.le_of_dvd (Nat.factorial_pos u.length) hDiv
    rw [← Nat.cast_prod]
    simp only [Complex.norm_natCast]
    exact_mod_cast hLe
  · simp

end CircularLaw
