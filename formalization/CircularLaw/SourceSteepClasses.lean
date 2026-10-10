import CircularLaw.OrderedNormAt
import CircularLaw.SteepScales

/-!
# The source very-steep and recursive `T0` classes

`sourceT0Previous` records the source `T3` class and all earlier first
jumps. The characterization below proves that `sourceT0ClassAt` has
exactly the exclusion of earlier classes in the manuscript, including
the distinct terminal ceiling jump. Source indices are one-based.
-/

noncomputable section
open Classical

namespace CircularLaw

def sourceT3 (n d L : ℕ) : Set (Fin n → ℂ) :=
  {x | ∃ i : ℕ, 0 < i ∧ i ≤ (steepStride d) ^ steepStartExponent (steepStride d) d L ∧
    ((n : ℝ) / i) ^ 3 *
      orderedNormAt x ((steepStride d) ^ steepStartExponent (steepStride d) d L) <
        orderedNormAt x i}

def sourceSteepPairAt (n d i : ℕ) : ℕ × ℕ :=
  if i < steepEndExponent (steepStride d) (firstSteepScale n d) then
    ((steepStride d) ^ i, (steepStride d) ^ (i + 1))
  else (terminalSteepSize (steepStride d) (firstSteepScale n d), firstSteepScale n d)

def sourceT0JumpAt (n d i : ℕ) (x : Fin n → ℂ) : Prop :=
  4 * (d : ℝ) * orderedNormAt x (sourceSteepPairAt n d i).2 <
    orderedNormAt x (sourceSteepPairAt n d i).1

def sourceT0Previous (n d L : ℕ) : ℕ → Set (Fin n → ℂ)
  | 0 => sourceT3 n d L
  | i + 1 => sourceT0Previous n d L i ∪
    {x | steepStartExponent (steepStride d) d L ≤ i ∧
      i ≤ steepEndExponent (steepStride d) (firstSteepScale n d) ∧
      x ∉ sourceT0Previous n d L i ∧ sourceT0JumpAt n d i x}

def sourceT0ClassAt (n d L i : ℕ) : Set (Fin n → ℂ) :=
  {x | steepStartExponent (steepStride d) d L ≤ i ∧
    i ≤ steepEndExponent (steepStride d) (firstSteepScale n d) ∧
    x ∉ sourceT0Previous n d L i ∧ sourceT0JumpAt n d i x}

def sourceT0 (n d L : ℕ) : Set (Fin n → ℂ) :=
  {x | ∃ i ∈ Finset.Icc (steepStartExponent (steepStride d) d L)
    (steepEndExponent (steepStride d) (firstSteepScale n d)), x ∈ sourceT0ClassAt n d L i}

def sourceShiftedT0 (n d L : ℕ) : Set (Fin n → ℂ) :=
  {v | ∃ (x : Fin n → ℂ) (c : ℂ), x ∈ sourceT0 n d L ∧
    ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10 ∧ v = fun j => x j + c}

theorem sourceT0Previous_succ (n d L i : ℕ) :
    sourceT0Previous n d L (i + 1) = sourceT0Previous n d L i ∪ sourceT0ClassAt n d L i := rfl

theorem mem_sourceT0Previous {n d L i : ℕ} (x : Fin n → ℂ) :
    x ∈ sourceT0Previous n d L i ↔
      x ∈ sourceT3 n d L ∨ ∃ j : ℕ, j < i ∧ x ∈ sourceT0ClassAt n d L j := by
  induction i with
  | zero => simp only [sourceT0Previous, Nat.not_lt_zero, false_and, exists_false, or_false]
  | succ i ih =>
    rw [sourceT0Previous_succ, Set.mem_union, ih]
    constructor
    · rintro ((h3 | ⟨j, hj, hx⟩) | hx)
      · exact Or.inl h3
      · exact Or.inr ⟨j, by omega, hx⟩
      · exact Or.inr ⟨i, by omega, hx⟩
    · rintro (h3 | ⟨j, hj, hx⟩)
      · exact Or.inl (Or.inl h3)
      · by_cases hji : j < i
        · exact Or.inl (Or.inr ⟨j, hji, hx⟩)
        · have hEq : j = i := by omega
          subst j
          exact Or.inr hx

theorem mem_sourceT0ClassAt_iff {n d L i : ℕ} (x : Fin n → ℂ) :
    x ∈ sourceT0ClassAt n d L i ↔
      steepStartExponent (steepStride d) d L ≤ i ∧
      i ≤ steepEndExponent (steepStride d) (firstSteepScale n d) ∧
      x ∉ sourceT3 n d L ∧
      (∀ j ∈ Finset.Ico (steepStartExponent (steepStride d) d L) i,
        x ∉ sourceT0ClassAt n d L j) ∧ sourceT0JumpAt n d i x := by
  change (_ ∧ _ ∧ x ∉ sourceT0Previous n d L i ∧ _) ↔ _
  rw [mem_sourceT0Previous]
  constructor
  · rintro ⟨hLo, hHi, hPrev, hJump⟩
    refine ⟨hLo, hHi, fun h3 => hPrev (Or.inl h3), ?_, hJump⟩
    intro j hj hx
    exact hPrev (Or.inr ⟨j, (Finset.mem_Ico.mp hj).2, hx⟩)
  · rintro ⟨hLo, hHi, h3, hPrev, hJump⟩
    refine ⟨hLo, hHi, ?_, hJump⟩
    rintro (hx3 | ⟨j, hj, hx⟩)
    · exact h3 hx3
    · have hLoJ := hx.1
      exact hPrev j (Finset.mem_Ico.mpr ⟨hLoJ, hj⟩) hx

theorem sourceSteepPairAt_mem {n d L i : ℕ}
    (hLo : steepStartExponent (steepStride d) d L ≤ i)
    (hHi : i ≤ steepEndExponent (steepStride d) (firstSteepScale n d)) :
    sourceSteepPairAt n d i ∈ sourceSteepScalePairs n d L := by
  unfold sourceSteepPairAt
  split
  · rename_i h
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_Ico.mpr ⟨hLo, h⟩, rfl⟩
  · rename_i hNot
    have hEq : i = steepEndExponent (steepStride d) (firstSteepScale n d) := by omega
    subst i
    apply Finset.mem_union_right
    exact Finset.mem_singleton_self _

theorem sourceT0_has_source_jump {n d L : ℕ} (x : Fin n → ℂ) (hx : x ∈ sourceT0 n d L) :
    ∃ a ∈ sourceSteepScalePairs n d L,
      4 * (d : ℝ) * orderedNormAt x a.2 < orderedNormAt x a.1 := by
  obtain ⟨i, hi, hx⟩ := hx
  obtain ⟨hLo, hHi⟩ := Finset.mem_Icc.mp hi
  exact ⟨sourceSteepPairAt n d i, sourceSteepPairAt_mem hLo hHi, hx.2.2.2⟩

end CircularLaw
