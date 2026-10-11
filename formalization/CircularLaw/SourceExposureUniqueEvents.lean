import CircularLaw.SourceExposureExpansionSeed
import CircularLaw.BlockedExpansionFailureSums
import CircularLaw.BernoulliBidirectionalGraphDegree

/-!
# Simultaneous unique expansion along the actual prefix exposures

The square prefix and the prefix with one extra column are tested at
the deterministic barrier seed. Their probabilities are summed over
the whole schedule, and adjoint invariance supplies the other direction.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix BigOperators NNReal

namespace CircularLaw

def SourceExposureUniqueBudgetAt {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (m : ℕ) (hm : m ≤ N) (β d : ℝ) : Prop :=
  MatrixUniqueExpansionBudget (A.submatrix (Fin.castLE hm) (Fin.castLE hm))
    (Function.Embedding.refl _) β N d (sourceExposureExpansionSeed N m) (sourceGraphTerminalScale N d) ∧
  ∀ hNext : m + 1 ≤ N, MatrixUniqueExpansionBudget
    (A.submatrix (Fin.castLE hm) (Fin.castLE hNext)) Fin.castSuccEmb β N d
      (sourceExposureExpansionSeed N (m + 1)) (sourceGraphTerminalScale N d)

def SourceExposureUniqueBudget {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (β d : ℝ) : Prop :=
  ∀ (m : ℕ) (hm : m ≤ N), 3 * (N : ℝ) / 4 ≤ m → SourceExposureUniqueBudgetAt A m hm β d

theorem bernoulli_source_exposure_unique_failure_at {N m : ℕ}
    (hN : 0 < N) (hm : m ≤ N) (hRows : 3 * (N : ℝ) / 4 ≤ m)
    (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 1024 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x |
      ¬ SourceExposureUniqueBudgetAt (bernoulliSquareMatrix x) m hm β d} ≤
      6 * Real.exp (-d * sourceExposureExpansionSeed N (m + 1) / 16) +
      2 * (N : ℝ) * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
  let r : Fin m ↪ Fin N := ⟨Fin.castLE hm, Fin.castLE_injective hm⟩
  let E₀ := {x : BernoulliSquareSample N | ¬ MatrixUniqueExpansionBudget
    ((bernoulliSquareMatrix x).submatrix (Fin.castLE hm) (Fin.castLE hm))
      (Function.Embedding.refl _) β N d (sourceExposureExpansionSeed N m) (sourceGraphTerminalScale N d)}
  let E₁ := {x : BernoulliSquareSample N | ∃ hNext : m + 1 ≤ N, ¬ MatrixUniqueExpansionBudget
    ((bernoulliSquareMatrix x).submatrix (Fin.castLE hm) (Fin.castLE hNext)) Fin.castSuccEmb β N d
      (sourceExposureExpansionSeed N (m + 1)) (sourceGraphTerminalScale N d)}
  have h₀ : (bernoulliSquareMatrixLaw N p hp).real E₀ ≤
      2 * Real.exp (-d * sourceExposureExpansionSeed N m / 16) +
        (N : ℝ) * Real.exp (-(N : ℝ) / (64 * Real.log d)) :=
    bernoulli_restricted_square_source_unique_expansion_failure hN hm
      (source_exposure_expansion_seed_pos N m) hRows r r p hp hHalf hDegree hd hβ hβOne
  have h₁ : (bernoulliSquareMatrixLaw N p hp).real E₁ ≤
      4 * Real.exp (-d * sourceExposureExpansionSeed N (m + 1) / 16) +
        (N : ℝ) * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
    by_cases hNext : m + 1 ≤ N
    · let c : Fin (m + 1) ↪ Fin N := ⟨Fin.castLE hNext, Fin.castLE_injective hNext⟩
      have hEvent : E₁ = {x : BernoulliSquareSample N | ¬ MatrixUniqueExpansionBudget
          ((bernoulliSquareMatrix x).submatrix (Fin.castLE hm) (Fin.castLE hNext)) Fin.castSuccEmb β N d
            (sourceExposureExpansionSeed N (m + 1)) (sourceGraphTerminalScale N d)} := by
        ext x
        constructor
        · rintro ⟨_, hBad⟩
          exact hBad
        · intro hBad
          exact ⟨hNext, hBad⟩
      rw [hEvent]
      exact bernoulli_restricted_rectangular_source_unique_expansion_failure hN hNext
        (source_exposure_expansion_seed_pos N (m + 1)) hRows r c p hp hHalf hDegree hd hβ hβOne
    · have hEmpty : E₁ = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨h, _⟩
        exact hNext h
      rw [hEmpty, measureReal_empty]
      positivity
  have hEvent : {x : BernoulliSquareSample N |
      ¬ SourceExposureUniqueBudgetAt (bernoulliSquareMatrix x) m hm β d} = E₀ ∪ E₁ := by
    ext x
    simp only [SourceExposureUniqueBudgetAt, E₀, E₁, Set.mem_setOf_eq, Set.mem_union, not_and_or, not_forall]
  rw [hEvent]
  have hSeed : sourceExposureExpansionSeed N (m + 1) ≤ sourceExposureExpansionSeed N m := by
    unfold sourceExposureExpansionSeed
    omega
  have hSeedReal : (sourceExposureExpansionSeed N (m + 1) : ℝ) ≤ sourceExposureExpansionSeed N m := by
    exact_mod_cast hSeed
  have hExp : Real.exp (-d * sourceExposureExpansionSeed N m / 16) ≤
      Real.exp (-d * sourceExposureExpansionSeed N (m + 1) / 16) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hSeedReal ((Real.exp_pos 1024).trans_le hd).le]
  exact (measureReal_union_le _ _).trans (by linarith)

theorem bernoulli_source_exposure_unique_failure {N : ℕ}
    (hN : 0 < N) (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 1024 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x |
      ¬ SourceExposureUniqueBudget (bernoulliSquareMatrix x) β d} ≤
      393222 * Real.exp (-d / 16) +
        2 * ((N + 1 : ℕ) : ℝ) * N * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
  let E := fun j : ℕ => {x : BernoulliSquareSample N |
    3 * (N : ℝ) / 4 ≤ (N - j : ℕ) ∧
      ¬ SourceExposureUniqueBudgetAt (bernoulliSquareMatrix x) (N - j) (Nat.sub_le N j) β d}
  have hFixed (j : ℕ) (hj : j ∈ Finset.range (N + 1)) :
      (bernoulliSquareMatrixLaw N p hp).real (E j) ≤
        6 * Real.exp (-d * (((j - 1) / 32768 + 1 : ℕ) : ℝ) / 16) +
        2 * N * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
    by_cases hRows : 3 * (N : ℝ) / 4 ≤ (N - j : ℕ)
    · have hJ : j ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      have hSeed : sourceExposureExpansionSeed N (N - j + 1) = (j - 1) / 32768 + 1 := by
        unfold sourceExposureExpansionSeed
        have hDiff : N - (N - j + 1) = j - 1 := by omega
        rw [hDiff]
      have h := bernoulli_source_exposure_unique_failure_at hN (Nat.sub_le N j) hRows p hp hHalf
        hDegree hd hβ hβOne
      rw [hSeed] at h
      exact (measureReal_mono (fun _ hx => hx.2) (measure_ne_top _ _)).trans h
    · have hEmpty : E j = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hRows hx.1
      rw [hEmpty, measureReal_empty]
      positivity
  have hSubset : {x : BernoulliSquareSample N | ¬ SourceExposureUniqueBudget (bernoulliSquareMatrix x) β d} ⊆
      ⋃ j ∈ Finset.range (N + 1), E j := by
    intro x hx
    simp only [SourceExposureUniqueBudget, not_forall, exists_prop] at hx
    obtain ⟨m, hm, hRows, hBad⟩ := hx
    have hDiff : N - (N - m) = m := by omega
    refine Set.mem_iUnion.mpr ⟨N - m, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    change 3 * (N : ℝ) / 4 ≤ (N - (N - m) : ℕ) ∧
      ¬ SourceExposureUniqueBudgetAt (bernoulliSquareMatrix x) (N - (N - m)) (Nat.sub_le N (N - m)) β d
    simpa only [hDiff] using And.intro hRows hBad
  calc
    _ ≤ (bernoulliSquareMatrixLaw N p hp).real (⋃ j ∈ Finset.range (N + 1), E j) :=
      measureReal_mono hSubset (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.range (N + 1), (bernoulliSquareMatrixLaw N p hp).real (E j) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (N + 1),
        (6 * Real.exp (-d * (((j - 1) / 32768 + 1 : ℕ) : ℝ) / 16) +
          2 * N * Real.exp (-(N : ℝ) / (64 * Real.log d))) := Finset.sum_le_sum hFixed
    _ = 6 * (∑ j ∈ Finset.range (N + 1), Real.exp (-d * (((j - 1) / 32768 + 1 : ℕ) : ℝ) / 16)) +
        ((N + 1 : ℕ) : ℝ) * (2 * N * Real.exp (-(N : ℝ) / (64 * Real.log d))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ _ := by
      have h := shifted_source_expansion_seed_exponential_sum_le
        (by linarith [(large_set_expansion_degree_range hd).1] : 16 ≤ d) N
      nlinarith

def BidirectionalSourceExposureUniqueBudget {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (β d : ℝ) : Prop := SourceExposureUniqueBudget A β d ∧ SourceExposureUniqueBudget Aᴴ β d

theorem bernoulli_bidirectional_source_exposure_unique_failure {N : ℕ}
    (hN : 0 < N) (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 1024 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x |
      ¬ BidirectionalSourceExposureUniqueBudget (bernoulliSquareMatrix x) β d} ≤
      786444 * Real.exp (-d / 16) +
        4 * ((N + 1 : ℕ) : ℝ) * N * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
  have hA := bernoulli_source_exposure_unique_failure hN p hp hHalf hDegree hd hβ hβOne
  have hAdj : (bernoulliSquareMatrixLaw N p hp).real {x |
      ¬ SourceExposureUniqueBudget (bernoulliSquareMatrix x)ᴴ β d} ≤
      393222 * Real.exp (-d / 16) +
        2 * ((N + 1 : ℕ) : ℝ) * N * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
    rw [bernoulli_square_adjoint_event_probability p hp (fun A => ¬ SourceExposureUniqueBudget A β d)]
    exact hA
  have hEvent : {x : BernoulliSquareSample N |
      ¬ BidirectionalSourceExposureUniqueBudget (bernoulliSquareMatrix x) β d} =
      {x | ¬ SourceExposureUniqueBudget (bernoulliSquareMatrix x) β d} ∪
        {x | ¬ SourceExposureUniqueBudget (bernoulliSquareMatrix x)ᴴ β d} := by
    ext x
    simp only [BidirectionalSourceExposureUniqueBudget, Set.mem_setOf_eq, Set.mem_union, not_and_or]
  rw [hEvent]
  exact (measureReal_union_le _ _).trans (by linarith)

def BidirectionalSourceExposureGraphBudget {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (β d : ℝ) : Prop :=
  BidirectionalGraphDegreeBudgets A 8 N d β ∧ BidirectionalSourceExposureUniqueBudget A β d

theorem bernoulli_bidirectional_source_exposure_graph_failure {N : ℕ}
    (hN : 0 < N) (p : ℝ≥0) (hp : p ≤ 1) (hHalf : (p : ℝ) ≤ 1 / 2) {d β : ℝ}
    (hDegree : d = (N : ℝ) * p) (hd : Real.exp 1024 ≤ d) (hβ : 0 < β) (hβOne : β ≤ 1) :
    (bernoulliSquareMatrixLaw N p hp).real {x |
      ¬ BidirectionalSourceExposureGraphBudget (bernoulliSquareMatrix x) β d} ≤
      2 * ((N : ℝ)⁻¹) ^ 3 + 786444 * Real.exp (-d / 16) +
        4 * ((N + 1 : ℕ) : ℝ) * N * Real.exp (-(N : ℝ) / (64 * Real.log d)) := by
  have hDegreeBudget := bernoulli_bidirectional_graph_degree_failure hN p hp
    (by rw [← hDegree]; linarith [(large_set_expansion_degree_range hd).1] : 32 ≤ (N : ℝ) * p) hβ hβOne
  rw [← hDegree] at hDegreeBudget
  have hUnique := bernoulli_bidirectional_source_exposure_unique_failure hN p hp hHalf hDegree hd hβ hβOne
  have hEvent : {x : BernoulliSquareSample N |
      ¬ BidirectionalSourceExposureGraphBudget (bernoulliSquareMatrix x) β d} =
      {x | ¬ BidirectionalGraphDegreeBudgets (bernoulliSquareMatrix x) 8 N d β} ∪
        {x | ¬ BidirectionalSourceExposureUniqueBudget (bernoulliSquareMatrix x) β d} := by
    ext x
    simp only [BidirectionalSourceExposureGraphBudget, Set.mem_setOf_eq, Set.mem_union, not_and_or]
  rw [hEvent]
  exact (measureReal_union_le _ _).trans (by linarith)

end CircularLaw
