import CircularLaw.DisjointSetPairs
import CircularLaw.WitnessCountTail
import CircularLaw.BinomialEntropy

/-!
# Failure probability for the uniform equal-block witness event

The union is over the actual disjoint coordinate-set pairs. Its cardinality
is counted exactly before applying the binomial entropy estimate.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem uniform_equal_block_failure_counting {n d s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (hRows : (n : ℝ) / 2 ≤ Fintype.card ι) (hSmall : 100 * d * s ≤ n)
    {cw : ℝ} (hcw : cw ≤ 1 / 4) :
    uniformProbability (fun rows : ι → RowSlice n d => ¬UniformEqualBlockWitness cw s rows) ≤
      (n.choose (2 * s) : ℝ) * (2 * s).choose s *
        Real.exp (-(binomialHalfRate / 2) * d * s) := by
  let E : DisjointSetPair n s (2 * s) → (ι → RowSlice n d) → Prop :=
    fun p rows => ((blockWitnessRows (p.val.1 ∪ p.val.2) rows).card : ℝ) < (d : ℝ) * s / 4
  have hEvent : ∀ rows : ι → RowSlice n d, ¬UniformEqualBlockWitness cw s rows →
      ∃ p ∈ (Finset.univ : Finset (DisjointSetPair n s (2 * s))), E p rows := by
    intro rows hBad
    unfold UniformEqualBlockWitness at hBad
    push_neg at hBad
    obtain ⟨L, R, hDis, hL, hR, hCount⟩ := hBad
    have hUnion : (L ∪ R).card = 2 * s := by
      rw [Finset.card_union_of_disjoint hDis, hL, hR]
      omega
    refine ⟨⟨(L, R), hDis, hL, hUnion⟩, Finset.mem_univ _, ?_⟩
    dsimp only [E]
    have hThreshold : cw * (d : ℝ) * s ≤ (d : ℝ) * s / 4 := by
      have hNonneg : (0 : ℝ) ≤ (d : ℝ) * s := by positivity
      nlinarith
    exact hCount.trans_le hThreshold
  apply (uniformProbability_mono hEvent).trans
  apply (uniformProbability_finset_exists_le Finset.univ E).trans
  calc
    _ ≤ ∑ _p : DisjointSetPair n s (2 * s),
        Real.exp (-(binomialHalfRate / 2) * d * s) := by
      apply Finset.sum_le_sum
      intro p _
      have hRight : p.val.2.card = s := by
        have hUnion := p.property.2.2
        rw [Finset.card_union_of_disjoint p.property.1, p.property.2.1] at hUnion
        omega
      exact small_equal_pair_witness_failure hn hd hdn p.val.1 p.val.2
        p.property.1 p.property.2.1 hRight hRows hSmall
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_disjoint_set_pairs,
        Nat.cast_mul]

theorem uniform_equal_block_failure_entropy {n d s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hn : 2 ≤ n) (hd : 0 < d) (hdn : d ≤ n)
    (hs : 0 < s) (hRows : (n : ℝ) / 2 ≤ Fintype.card ι) (hSmall : 100 * d * s ≤ n)
    {cw : ℝ} (hcw : cw ≤ 1 / 4) :
    uniformProbability (fun rows : ι → RowSlice n d => ¬UniformEqualBlockWitness cw s rows) ≤
      Real.exp (-(binomialHalfRate / 2) * d * s + (2 * s : ℕ) *
        (Real.log (Real.exp 1 * n / (2 * s : ℕ)) + Real.log 2)) := by
  have ht : 0 < 2 * s := by omega
  have htn : 2 * s ≤ n := by nlinarith
  have hEntropy := choose_pair_entropy (by omega : 0 < n) ht htn (s := s)
  apply (uniform_equal_block_failure_counting hn hd hdn hRows hSmall hcw).trans
  apply (mul_le_mul_of_nonneg_right hEntropy (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

end CircularLaw
