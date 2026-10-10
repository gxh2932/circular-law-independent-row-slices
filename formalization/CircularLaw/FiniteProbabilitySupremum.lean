import CircularLaw.CanonicalFamilyProbability
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# The manuscript's sum of fixed-vector probability suprema

Every event probability on a finite sample space belongs to a finite
set of values. Hence its supremum over deterministic shifts is attained.
A single shift assignment realizes all maxima of a finite vector family.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem uniformProbability_range_finite {α β : Type*} [Fintype α]
    (event : β → α → Prop) : (Set.range (fun b => uniformProbability (event b))).Finite := by
  apply (Set.finite_range (fun S : Finset α => (S.card : ℝ) / Nat.card α)).subset
  rintro p ⟨b, rfl⟩
  refine ⟨Finset.univ.filter (event b), ?_⟩
  simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem uniformProbability_ciSup_attained {α β : Type*} [Fintype α] [Nonempty β]
    (event : β → α → Prop) :
    ∃ b, uniformProbability (event b) = ⨆ t, uniformProbability (event t) :=
  (Set.range_nonempty (fun b => uniformProbability (event b))).csSup_mem
    (uniformProbability_range_finite event)

def canonicalFamilySupProbabilitySum {n : ℕ} (A : Set (Fin n → ℂ)) [Fintype A]
    (I : Finset (Fin n)) (k d : ℕ) (R : ℝ) : ℝ :=
  ∑ y : A, ⨆ V : I → ℂ, uniformProbability (fun rows : RowSliceMatrix n d =>
    indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y.val V ≤
      R * Real.log d * Real.sqrt ((d : ℝ) * n) / k)

theorem canonicalFamilySupProbabilitySum_eq_choice {n : ℕ}
    (A : Set (Fin n → ℂ)) [Fintype A] (I : Finset (Fin n)) (k d : ℕ) (R : ℝ) :
    ∃ V : (Fin n → ℂ) → I → ℂ,
      canonicalFamilySupProbabilitySum A I k d R = canonicalFamilyProbabilitySum A I k d R V := by
  have hMax (y : A) := uniformProbability_ciSup_attained (fun (V : I → ℂ) (rows : RowSliceMatrix n d) =>
    indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y.val V ≤
      R * Real.log d * Real.sqrt ((d : ℝ) * n) / k)
  choose W hW using hMax
  let V : (Fin n → ℂ) → I → ℂ := fun y => if hy : y ∈ A then W ⟨y, hy⟩ else 0
  refine ⟨V, ?_⟩
  unfold canonicalFamilySupProbabilitySum canonicalFamilyProbabilitySum
  apply Finset.sum_congr rfl
  intro y _
  simp only [V, dif_pos y.property]
  exact (hW y).symm

theorem canonicalFamilySupProbabilitySum_le {n : ℕ}
    (A : Set (Fin n → ℂ)) [Fintype A] (I : Finset (Fin n)) (k d : ℕ) (R B : ℝ)
    (h : ∀ V : (Fin n → ℂ) → I → ℂ, canonicalFamilyProbabilitySum A I k d R V ≤ B) :
    canonicalFamilySupProbabilitySum A I k d R ≤ B := by
  obtain ⟨V, hV⟩ := canonicalFamilySupProbabilitySum_eq_choice A I k d R
  rw [hV]
  exact h V

theorem canonicalFamilySupProbabilitySum_nonneg {n : ℕ}
    (A : Set (Fin n → ℂ)) [Fintype A] (I : Finset (Fin n)) (k d : ℕ) (R : ℝ) :
    0 ≤ canonicalFamilySupProbabilitySum A I k d R := by
  obtain ⟨V, hV⟩ := canonicalFamilySupProbabilitySum_eq_choice A I k d R
  rw [hV]
  exact Finset.sum_nonneg (fun y _ => uniformProbability_nonneg _)

theorem canonicalFamilySupProbabilitySum_congr_set {n : ℕ}
    {A B : Set (Fin n → ℂ)} [hA : Fintype A] [hB : Fintype B] (h : A = B)
    (I : Finset (Fin n)) (k d : ℕ) (R : ℝ) :
    canonicalFamilySupProbabilitySum A I k d R = canonicalFamilySupProbabilitySum B I k d R := by
  cases h
  have hInst : hA = hB := Subsingleton.elim _ _
  cases hInst
  rfl

theorem finite_family_sum_union_le {α : Type*} (A B : Set α)
    [Fintype A] [Fintype B] [Fintype (A ∪ B : Set α)] (f : α → ℝ)
    (hNonneg : ∀ x ∈ A ∪ B, 0 ≤ f x) :
    (∑ x : (A ∪ B : Set α), f x.val) ≤ (∑ x : A, f x.val) + ∑ x : B, f x.val := by
  rw [Finset.sum_set_coe, Finset.sum_set_coe, Finset.sum_set_coe, Set.toFinset_union]
  have h := Finset.sum_union_inter (s₁ := A.toFinset) (s₂ := B.toFinset) (f := f)
  have hInter : 0 ≤ ∑ x ∈ A.toFinset ∩ B.toFinset, f x := by
    apply Finset.sum_nonneg
    intro x hx
    exact hNonneg x (Or.inl (Set.mem_toFinset.mp (Finset.mem_inter.mp hx).1))
  linarith

theorem canonicalFamilySupProbabilitySum_union_le {n : ℕ}
    (A B : Set (Fin n → ℂ)) [Fintype A] [Fintype B] [Fintype (A ∪ B : Set (Fin n → ℂ))]
    (I : Finset (Fin n)) (k d : ℕ) (R : ℝ) :
    canonicalFamilySupProbabilitySum (A ∪ B) I k d R ≤
      canonicalFamilySupProbabilitySum A I k d R + canonicalFamilySupProbabilitySum B I k d R := by
  unfold canonicalFamilySupProbabilitySum
  apply finite_family_sum_union_le A B (fun y => ⨆ V : I → ℂ,
    uniformProbability (fun rows : RowSliceMatrix n d =>
      indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y V ≤
        R * Real.log d * Real.sqrt ((d : ℝ) * n) / k))
  intro y _
  obtain ⟨V, hV⟩ := uniformProbability_ciSup_attained (fun (V : I → ℂ) (rows : RowSliceMatrix n d) =>
    indexedSliceMatrixVectorL2Norm (fun i : I => rows i.val) y V ≤
      R * Real.log d * Real.sqrt ((d : ℝ) * n) / k)
  rw [← hV]
  exact uniformProbability_nonneg _

end CircularLaw
