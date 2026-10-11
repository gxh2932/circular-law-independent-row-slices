import CircularLaw.HypergeometricRelativeTail
import CircularLaw.UniformEmbeddingMarginal

/-!
# Occupancy tails for exact uniform injective samples

Support counting transports the relative hypergeometric lower tail to
injections. Domain and population equivalences keep the bound valid on
the actual complement population exposed by the first half of a pair
sample, and restriction handles arbitrary selected pair indices.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def embeddingHitCount {α β : Type*} [Fintype α] (e : α ↪ β) (M : Finset β) : ℕ :=
  (Finset.univ.filter (fun a => e a ∈ M)).card

def embeddingReindexEquiv {α β γ δ : Type*} (p : α ≃ γ) (q : β ≃ δ) :
    (α ↪ β) ≃ (γ ↪ δ) where
  toFun e := p.symm.toEmbedding.trans (e.trans q.toEmbedding)
  invFun e := p.toEmbedding.trans (e.trans q.symm.toEmbedding)
  left_inv e := by ext a; simp
  right_inv e := by ext a; simp

theorem embedding_hit_count_reindex {α β γ δ : Type*} [Fintype α] [Fintype γ]
    (p : α ≃ γ) (q : β ≃ δ) (e : α ↪ β) (M : Finset β) :
    embeddingHitCount (embeddingReindexEquiv p q e) (M.map q.toEmbedding) =
      embeddingHitCount e M := by
  unfold embeddingHitCount
  symm
  refine Finset.card_bij' (fun a _ => p a) (fun b _ => p.symm b) ?_ ?_ ?_ ?_
  · intro a ha
    simpa [embeddingReindexEquiv] using ha
  · intro b hb
    simpa [embeddingReindexEquiv] using hb
  · intro a _
    exact p.symm_apply_apply a
  · intro b _
    exact p.apply_symm_apply b

theorem embedding_hit_count_eq_slice_occupancy {n d : ℕ} (e : Fin d ↪ Fin n)
    (M : Finset (Fin n)) : embeddingHitCount e M = ((sliceOfEmbedding e).val ∩ M).card := by
  have hMap : (Finset.univ.filter (fun a => e a ∈ M)).map e = (sliceOfEmbedding e).val ∩ M := by
    ext j
    simp only [sliceOfEmbedding, Finset.mem_inter, Finset.mem_map,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, rfl⟩, ha⟩
    · rintro ⟨⟨a, rfl⟩, ha⟩
      exact ⟨a, ha, rfl⟩
  have hCard := congrArg Finset.card hMap
  rw [Finset.card_map] at hCard
  convert hCard using 1
  unfold embeddingHitCount
  congr 1
  ext a
  simp

theorem uniform_fin_embedding_occupancy_relative_lower_tail {n d : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) (M : Finset (Fin n)) :
    uniformProbability (fun e : Fin d ↪ Fin n =>
      (embeddingHitCount e M : ℝ) ≤ ((d : ℝ) / n) * M.card / 2) ≤
        Real.exp (-(((d : ℝ) / n) * M.card) / 12) := by
  have h := slice_occupancy_relative_lower_tail hn hdn M
  rw [← uniform_embedding_support] at h
  simpa only [embedding_hit_count_eq_slice_occupancy] using h

theorem uniform_embedding_occupancy_relative_lower_tail {α β : Type*}
    [Fintype α] [Fintype β] (hPopulation : 0 < Fintype.card β)
    (hSize : Fintype.card α ≤ Fintype.card β) (M : Finset β) :
    uniformProbability (fun e : α ↪ β => (embeddingHitCount e M : ℝ) ≤
      ((Fintype.card α : ℝ) / Fintype.card β) * M.card / 2) ≤
        Real.exp (-(((Fintype.card α : ℝ) / Fintype.card β) * M.card) / 12) := by
  let p := Fintype.equivFin α
  let q := Fintype.equivFin β
  have h := uniform_fin_embedding_occupancy_relative_lower_tail hPopulation hSize
    (M.map q.toEmbedding)
  rw [← uniformProbability_reindex (embeddingReindexEquiv p q)] at h
  simpa only [embedding_hit_count_reindex, Finset.card_map] using h

theorem uniform_embedding_occupancy_half_population_lower_tail {α β : Type*}
    [Fintype α] [Fintype β] (hPopulation : 0 < Fintype.card β)
    (hSize : Fintype.card α ≤ Fintype.card β) (M : Finset β)
    (hHalf : (Fintype.card β : ℝ) / 2 ≤ M.card) :
    uniformProbability (fun e : α ↪ β =>
      (embeddingHitCount e M : ℝ) ≤ (Fintype.card α : ℝ) / 4) ≤
        Real.exp (-(Fintype.card α : ℝ) / 24) := by
  have hPopulationR : (0 : ℝ) < Fintype.card β := by exact_mod_cast hPopulation
  have hMean := mul_le_mul_of_nonneg_left hHalf
    (by positivity : 0 ≤ (Fintype.card α : ℝ) / Fintype.card β)
  have hCancel : ((Fintype.card α : ℝ) / Fintype.card β) * ((Fintype.card β : ℝ) / 2) =
      (Fintype.card α : ℝ) / 2 := by field_simp
  rw [hCancel] at hMean
  apply (uniformProbability_mono ?_).trans
    ((uniform_embedding_occupancy_relative_lower_tail hPopulation hSize M).trans ?_)
  · intro e he
    linarith
  · apply Real.exp_le_exp.mpr
    linarith

theorem embedding_hit_count_restrict_finset {α β : Type*} [Fintype α]
    (H : Finset α) (e : α ↪ β) (M : Finset β) :
    embeddingHitCount ((Function.Embedding.subtype (fun a => a ∈ H)).trans e) M =
      (H.filter (fun a => e a ∈ M)).card := by
  unfold embeddingHitCount
  rw [Finset.card_filter, Finset.card_filter]
  exact Finset.sum_coe_sort H (fun a => if e a ∈ M then 1 else 0)

end CircularLaw
