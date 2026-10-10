import CircularLaw.UniformEmbeddingOccupancy
import CircularLaw.PairedSliceSmallBall

/-!
# Conditional occupancy of separated coordinate blocks

After fixing the first half of an injective pair sample, its second
half is an exact uniform injection into the unused population. A block
containing at least three quarters of all coordinates still occupies
at least half of that population when at most half was exposed.
-/

noncomputable section
open Classical

namespace CircularLaw

def embeddingComplementBlock {n d : ℕ} (u : Fin d ↪ Fin n) (R : Finset (Fin n)) :
    Finset ↥(Set.range u)ᶜ := Finset.univ.filter (fun j => j.val ∈ R)

def pairedBlockCoordinates {n d : ℕ} (L R : Finset (Fin n))
    (e : Fin d ⊕ Fin d ↪ Fin n) : Finset (Fin d) :=
  Finset.univ.filter (fun j => e (Sum.inl j) ∈ L ∧ e (Sum.inr j) ∈ R)

theorem sum_left_embedding_fiber_inverse_inl {α β γ : Type*} (u : α ↪ γ)
    (v : β ↪ ↥(Set.range u)ᶜ) (a : α) :
    ((sumLeftEmbeddingFiberEquiv u).symm v).val (Sum.inl a) = u a := rfl

theorem sum_left_embedding_fiber_inverse_inr {α β γ : Type*} (u : α ↪ γ)
    (v : β ↪ ↥(Set.range u)ᶜ) (b : β) :
    ((sumLeftEmbeddingFiberEquiv u).symm v).val (Sum.inr b) = (v b).val := rfl

theorem embedding_complement_block_card_lower {n d : ℕ} (u : Fin d ↪ Fin n)
    (R : Finset (Fin n)) : R.card ≤ (embeddingComplementBlock u R).card + d := by
  let U := Finset.univ.map u
  have hMap : (embeddingComplementBlock u R).map (Function.Embedding.subtype _) = R \ U := by
    ext j
    simp only [Finset.mem_map, Finset.mem_sdiff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨(Finset.mem_filter.mp ha).2, ?_⟩
      intro haU
      obtain ⟨i, _, hEq⟩ := Finset.mem_map.mp haU
      exact a.property ⟨i, hEq⟩
    · rintro ⟨hjR, hjU⟩
      have hjRange : j ∈ (Set.range u)ᶜ := by
        rintro ⟨i, rfl⟩
        exact hjU (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      exact ⟨⟨j, hjRange⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjR⟩, rfl⟩
  have hCard : (embeddingComplementBlock u R).card = (R \ U).card := by
    simpa only [Finset.card_map] using congrArg Finset.card hMap
  have hU : U.card = d := by simp [U]
  have hInter : (R ∩ U).card ≤ d := (Finset.card_le_card Finset.inter_subset_right).trans_eq hU
  rw [hCard]
  have hPartition := Finset.card_sdiff_add_card_inter R U
  omega

theorem embedding_complement_block_half_population {n d : ℕ}
    (hSize : 2 * d ≤ n) (u : Fin d ↪ Fin n) (R : Finset (Fin n))
    (hR : 3 * (n : ℝ) / 4 ≤ R.card) :
    (Fintype.card ↥(Set.range u)ᶜ : ℝ) / 2 ≤ (embeddingComplementBlock u R).card := by
  have hCard : (R.card : ℝ) ≤ (embeddingComplementBlock u R).card + d :=
    by exact_mod_cast embedding_complement_block_card_lower u R
  rw [embedding_range_complement_card, Nat.cast_sub (by omega : d ≤ n)]
  have hSizeR : 2 * (d : ℝ) ≤ n := by exact_mod_cast hSize
  linarith

theorem paired_block_fixed_left_count {n d : ℕ} (L R : Finset (Fin n))
    (u : Fin d ↪ Fin n) (v : Fin d ↪ ↥(Set.range u)ᶜ) :
    (pairedBlockCoordinates L R ((sumLeftEmbeddingFiberEquiv u).symm v).val).card =
      ((Finset.univ.filter (fun j => u j ∈ L)).filter (fun j => (v j).val ∈ R)).card := by
  congr 1
  ext j
  simp [pairedBlockCoordinates, sum_left_embedding_fiber_inverse_inl,
    sum_left_embedding_fiber_inverse_inr]

theorem paired_block_conditional_lower_tail {n d : ℕ} (hn : 0 < n)
    (hSize : 2 * d ≤ n) (L R : Finset (Fin n)) (hR : 3 * (n : ℝ) / 4 ≤ R.card)
    (u : Fin d ↪ Fin n) :
    uniformProbability (fun e : {e : Fin d ⊕ Fin d ↪ Fin n // Function.Embedding.inl.trans e = u} =>
      ((pairedBlockCoordinates L R e.val).card : ℝ) ≤ (embeddingHitCount u L : ℝ) / 4) ≤
        Real.exp (-(embeddingHitCount u L : ℝ) / 24) := by
  let H := Finset.univ.filter (fun j => u j ∈ L)
  let M := embeddingComplementBlock u R
  have hPopulation : 0 < Fintype.card ↥(Set.range u)ᶜ := by
    rw [embedding_range_complement_card]
    omega
  have hFullSize : Fintype.card (Fin d) ≤ Fintype.card ↥(Set.range u)ᶜ := by
    rw [Fintype.card_fin, embedding_range_complement_card]
    omega
  have hSelectedSize : Fintype.card H ≤ Fintype.card ↥(Set.range u)ᶜ := by
    rw [Fintype.card_coe]
    exact (Finset.card_filter_le _ _).trans (by
      simpa only [Finset.card_univ] using hFullSize)
  have hTail := uniform_embedding_occupancy_half_population_lower_tail hPopulation hSelectedSize M
    (embedding_complement_block_half_population hSize u R hR)
  have hLaw := uniform_embedding_restriction (Function.Embedding.subtype (fun j => j ∈ H))
    hFullSize (fun v : H ↪ ↥(Set.range u)ᶜ =>
      (embeddingHitCount v M : ℝ) ≤ (H.card : ℝ) / 4)
  rw [Fintype.card_coe] at hTail
  rw [← hLaw] at hTail
  have hCount (v : Fin d ↪ ↥(Set.range u)ᶜ) :
      embeddingHitCount ((Function.Embedding.subtype (fun j => j ∈ H)).trans v) M =
        (pairedBlockCoordinates L R ((sumLeftEmbeddingFiberEquiv u).symm v).val).card := by
    rw [embedding_hit_count_restrict_finset, paired_block_fixed_left_count]
    congr 1
    ext j
    simp [H, M, embeddingComplementBlock]
  rw [← uniformProbability_reindex (sumLeftEmbeddingFiberEquiv u).symm]
  simp_rw [hCount] at hTail
  have hH : embeddingHitCount u L = H.card := by
    unfold embeddingHitCount
    congr 1
    ext j
    simp [H]
  simpa only [hH] using hTail

end CircularLaw
