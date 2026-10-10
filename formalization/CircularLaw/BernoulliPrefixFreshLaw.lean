import CircularLaw.BernoulliFreshConditionalExpectation

/-!
# Fresh rows and columns of the actual ambient Bernoulli matrix

The upper-left rectangular prefix and its next row or column use
disjoint ambient entry coordinates. The conditional failure probability
of either insertion is exactly its fresh-vector Bernoulli probability,
with the currently exposed prefix fixed.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CircularLaw

def bernoulliPrefixEntryEmbedding {N a m : ℕ} (ha : a ≤ N) (hm : m ≤ N) :
    Fin a × Fin m ↪ Fin N × Fin N :=
  ⟨fun ij => (Fin.castLE ha ij.1, Fin.castLE hm ij.2), by
    intro i j h
    exact Prod.ext ((Fin.castLE_injective ha) (congrArg Prod.fst h))
      ((Fin.castLE_injective hm) (congrArg Prod.snd h))⟩

def bernoulliFreshRowEntryEmbedding {N a m : ℕ} (hNext : a + 1 ≤ N) (hm : m ≤ N) :
    Fin m ↪ Fin N × Fin N :=
  ⟨fun j => (Fin.castLE hNext (Fin.last a), Fin.castLE hm j), by
    intro i j h
    exact (Fin.castLE_injective hm) (congrArg Prod.snd h)⟩

def bernoulliFreshColumnEntryEmbedding {N a m : ℕ} (ha : a ≤ N) (hNext : m + 1 ≤ N) :
    Fin a ↪ Fin N × Fin N :=
  ⟨fun i => (Fin.castLE ha i, Fin.castLE hNext (Fin.last m)), by
    intro i j h
    exact (Fin.castLE_injective ha) (congrArg Prod.fst h)⟩

theorem bernoulli_prefix_fresh_row_disjoint {N a m : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (hNext : a + 1 ≤ N)
    (i : Fin a × Fin m) (j : Fin m) :
    bernoulliPrefixEntryEmbedding ha hm i ≠ bernoulliFreshRowEntryEmbedding hNext hm j := by
  intro h
  have hValue := congrArg (fun ij : Fin N × Fin N => ij.1.val) h
  change i.1.val = a at hValue
  exact (Nat.ne_of_lt i.1.isLt) hValue

theorem bernoulli_prefix_fresh_column_disjoint {N a m : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (hNext : m + 1 ≤ N)
    (i : Fin a × Fin m) (j : Fin a) :
    bernoulliPrefixEntryEmbedding ha hm i ≠ bernoulliFreshColumnEntryEmbedding ha hNext j := by
  intro h
  have hValue := congrArg (fun ij : Fin N × Fin N => ij.2.val) h
  change i.2.val = m at hValue
  exact (Nat.ne_of_lt i.2.isLt) hValue

theorem bernoulli_prefix_fresh_row_independent {N a m : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (hNext : a + 1 ≤ N) (p : ℝ≥0) (hp : p ≤ 1) :
    IndepFun (fun x : BernoulliSquareSample N =>
      fun ij => x (bernoulliPrefixEntryEmbedding ha hm ij))
      (fun x : BernoulliSquareSample N =>
        fun j => x (bernoulliFreshRowEntryEmbedding hNext hm j))
      (bernoulliSquareMatrixLaw N p hp) :=
  bernoulli_cube_disjoint_blocks_independent p hp _ _
    (bernoulli_prefix_fresh_row_disjoint ha hm hNext)

theorem bernoulli_prefix_fresh_column_independent {N a m : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (hNext : m + 1 ≤ N) (p : ℝ≥0) (hp : p ≤ 1) :
    IndepFun (fun x : BernoulliSquareSample N =>
      fun ij => x (bernoulliPrefixEntryEmbedding ha hm ij))
      (fun x : BernoulliSquareSample N =>
        fun i => x (bernoulliFreshColumnEntryEmbedding ha hNext i))
      (bernoulliSquareMatrixLaw N p hp) :=
  bernoulli_cube_disjoint_blocks_independent p hp _ _
    (bernoulli_prefix_fresh_column_disjoint ha hm hNext)

theorem bernoulli_prefix_fresh_row_conditional_probability {N a m : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (hNext : a + 1 ≤ N) (p : ℝ≥0) (hp : p ≤ 1)
    (B : (Fin a × Fin m → Bool) → (Fin m → Bool) → Prop) :
    (bernoulliSquareMatrixLaw N p hp)[
      ({x | B (fun ij => x (bernoulliPrefixEntryEmbedding ha hm ij))
        (fun j => x (bernoulliFreshRowEntryEmbedding hNext hm j))}).indicator
          (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap (fun x : BernoulliSquareSample N =>
          fun ij => x (bernoulliPrefixEntryEmbedding ha hm ij)) inferInstance] =ᵐ[
            bernoulliSquareMatrixLaw N p hp]
              fun x => (bernoulliCubeLaw (Fin m) p hp).real
                {y | B (fun ij => x (bernoulliPrefixEntryEmbedding ha hm ij)) y} :=
  bernoulli_disjoint_fresh_conditional_probability p hp _ _
    (bernoulli_prefix_fresh_row_disjoint ha hm hNext) B

theorem bernoulli_prefix_fresh_column_conditional_probability {N a m : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (hNext : m + 1 ≤ N) (p : ℝ≥0) (hp : p ≤ 1)
    (B : (Fin a × Fin m → Bool) → (Fin a → Bool) → Prop) :
    (bernoulliSquareMatrixLaw N p hp)[
      ({x | B (fun ij => x (bernoulliPrefixEntryEmbedding ha hm ij))
        (fun i => x (bernoulliFreshColumnEntryEmbedding ha hNext i))}).indicator
          (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap (fun x : BernoulliSquareSample N =>
          fun ij => x (bernoulliPrefixEntryEmbedding ha hm ij)) inferInstance] =ᵐ[
            bernoulliSquareMatrixLaw N p hp]
              fun x => (bernoulliCubeLaw (Fin a) p hp).real
                {y | B (fun ij => x (bernoulliPrefixEntryEmbedding ha hm ij)) y} :=
  bernoulli_disjoint_fresh_conditional_probability p hp _ _
    (bernoulli_prefix_fresh_column_disjoint ha hm hNext) B

end CircularLaw
