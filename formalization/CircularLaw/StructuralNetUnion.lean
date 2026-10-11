import CircularLaw.StructuralDiscretization
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Counting the actual union over terminal discretization scales

The index set is exactly `4 <= u <= vL`. Overlaps between the grids
can only decrease its cardinality. Restricted families may vary with u.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def structuralNetUnion {n : ℕ} (d v : ℕ) (X : ℕ → Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  ⋃ u ∈ Finset.Icc 4 v, canonicalApproxFamily (d ^ u) (X u)

theorem structuralNetUnion_count {n d v : ℕ} (X : ℕ → Set (Fin n → ℂ)) {E : ℝ}
    (hE : 0 ≤ E)
    (hFamilies : ∀ u ∈ Finset.Icc 4 v, (canonicalApproxFamily (d ^ u) (X u)).Finite ∧
      (Nat.card (canonicalApproxFamily (d ^ u) (X u)) : ℝ) ≤ E) :
    (structuralNetUnion d v X).Finite ∧
      (Nat.card (structuralNetUnion d v X) : ℝ) ≤ (v : ℝ) * E := by
  have hFinite : (structuralNetUnion d v X).Finite :=
    (Finset.Icc 4 v).finite_toSet.biUnion (fun u hu => (hFamilies u hu).1)
  have hCard : Nat.card (structuralNetUnion d v X) ≤
      ∑ u ∈ Finset.Icc 4 v, Nat.card (canonicalApproxFamily (d ^ u) (X u)) := by
    simpa only [structuralNetUnion, Nat.card_coe_set_eq] using
      (Finset.Icc 4 v).set_ncard_biUnion_le (fun u => canonicalApproxFamily (d ^ u) (X u))
  have hReal : (Nat.card (structuralNetUnion d v X) : ℝ) ≤
      ∑ u ∈ Finset.Icc 4 v, (Nat.card (canonicalApproxFamily (d ^ u) (X u)) : ℝ) := by
    exact_mod_cast hCard
  have hIndex : (Finset.Icc 4 v).card ≤ v := by rw [Nat.card_Icc]; omega
  refine ⟨hFinite, hReal.trans ?_⟩
  calc
    _ ≤ ∑ _u ∈ Finset.Icc 4 v, E := Finset.sum_le_sum (fun u hu => (hFamilies u hu).2)
    _ = ((Finset.Icc 4 v).card : ℝ) * E := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hIndex) hE

theorem eventually_structuralNetUnion_count_uniform {C : ℝ} (hC : 96 ≤ C) (σ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L → ∀ a₃ : ℝ,
      ∀ X : ℕ → Set (Fin n → ℂ), (∀ u, X u ⊆ sourceGradual n d L a₃) →
      (structuralNetUnion d (structuralTerminalExponent n d L) X).Finite ∧
      (Nat.card (structuralNetUnion d (structuralTerminalExponent n d L) X) : ℝ) ≤
        (structuralTerminalExponent n d L : ℝ) *
          Real.exp (128 * (n : ℝ) * Real.rpow (d : ℝ) (1 / 3)) := by
  filter_upwards [eventually_structuralGradualNet_count_uniform hC σ] with n hCount
  intro d hBand L hL a₃ X hX
  apply structuralNetUnion_count X (Real.exp_nonneg _)
  intro u hu
  exact hCount d hBand L hL a₃ u (Finset.mem_Icc.mp hu).2 (X u) (hX u)

end CircularLaw
