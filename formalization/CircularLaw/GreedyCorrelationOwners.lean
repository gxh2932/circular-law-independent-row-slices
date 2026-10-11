import CircularLaw.GreedyCorrelationClusters

/-!
# Representative lookup on the actual greedy exceptional set

Each discarded index belongs to a unique earlier star. Its representative
is one of the previously constructed representative indices and is related
to it in the original relation. The lookup is extended by the identity
outside the exceptional set.
-/

noncomputable section
open Classical

namespace CircularLaw

theorem greedyCorrelationExceptional_mem_stage {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) {j : Fin n}
    (hj : j ∈ greedyCorrelationExceptional R hR b) :
    ∃ k : Fin (greedyCorrelationStop R hR b), j ∈ greedyCorrelationStage R k.val := by
  rw [greedyCorrelationExceptional_eq_union] at hj
  obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp hj
  exact ⟨⟨k, Finset.mem_range.mp hk⟩, hjk⟩

def greedyCorrelationOwner {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) (j : Fin n)
    (hj : j ∈ greedyCorrelationExceptional R hR b) : Fin (greedyCorrelationStop R hR b) :=
  Classical.choose (greedyCorrelationExceptional_mem_stage R hR b hj)

theorem greedyCorrelationOwner_mem {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) (j : Fin n)
    (hj : j ∈ greedyCorrelationExceptional R hR b) :
    j ∈ greedyCorrelationStage R (greedyCorrelationOwner R hR b j hj).val :=
  Classical.choose_spec (greedyCorrelationExceptional_mem_stage R hR b hj)

theorem greedyCorrelationOwner_unique {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) (j : Fin n)
    (hj : j ∈ greedyCorrelationExceptional R hR b)
    (k : Fin (greedyCorrelationStop R hR b)) (hk : j ∈ greedyCorrelationStage R k.val) :
    k = greedyCorrelationOwner R hR b j hj := by
  apply Fin.ext
  have hOwner := greedyCorrelationOwner_mem R hR b j hj
  by_contra hNe
  rcases lt_or_gt_of_ne hNe with hLt | hGt
  · exact (Finset.disjoint_left.mp (greedyCorrelationStage_pairwise_disjoint R hLt)) hk hOwner
  · exact (Finset.disjoint_left.mp (greedyCorrelationStage_pairwise_disjoint R hGt)) hOwner hk

def greedyCorrelationRepresentativeAt {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) (j : Fin n) : Fin n :=
  if hj : j ∈ greedyCorrelationExceptional R hR b then
    greedyCorrelationRepresentative R hR b (greedyCorrelationOwner R hR b j hj)
  else j

theorem greedyCorrelationRepresentativeAt_eq {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) (j : Fin n)
    (hj : j ∈ greedyCorrelationExceptional R hR b) :
    greedyCorrelationRepresentativeAt R hR b j =
      greedyCorrelationRepresentative R hR b (greedyCorrelationOwner R hR b j hj) := by
  simp only [greedyCorrelationRepresentativeAt, dif_pos hj]

theorem greedyCorrelationRepresentativeAt_related {n : ℕ} (R : Fin n → Fin n → Prop)
    (hR : ∀ i, R i i) (b : ℕ) (j : Fin n)
    (hj : j ∈ greedyCorrelationExceptional R hR b) :
    R (greedyCorrelationRepresentativeAt R hR b j) j := by
  rw [greedyCorrelationRepresentativeAt_eq R hR b j hj]
  exact (greedyCorrelationRepresentative_spec R hR b _).2 j
    (greedyCorrelationOwner_mem R hR b j hj)

theorem greedyCorrelationRepresentativeAt_common_value {n : ℕ} {γ : Type*}
    (R : Fin n → Fin n → Prop) (hR : ∀ i, R i i) (b : ℕ)
    (y : Fin n → γ) (w : γ)
    (hRep : ∀ k : Fin (greedyCorrelationStop R hR b), y (greedyCorrelationRepresentative R hR b k) = w)
    (j : Fin n) (hj : j ∈ greedyCorrelationExceptional R hR b) :
    y (greedyCorrelationRepresentativeAt R hR b j) = w := by
  rw [greedyCorrelationRepresentativeAt_eq R hR b j hj]
  exact hRep _

end CircularLaw
