import CircularLaw.PermittedSteepShift

/-!
# The remaining literal source classes

The second and third ranks retain their floors. The `T1` and `T2`
exclusions, almost-constant class, and `S(t)` are the manuscript's
definitions, expressed with the actual one-based ordered moduli.
-/

noncomputable section
open Classical

namespace CircularLaw

def secondSteepScale (n d : ℕ) : ℕ := ⌊(n : ℝ) / Real.rpow (d : ℝ) (2 / 3)⌋₊

def thirdSteepScale (n : ℕ) (a₃ : ℝ) : ℕ := ⌊a₃ * (n : ℝ)⌋₊

def almostConstantRank (n d : ℕ) : ℕ := n / (16 * d)

def almostConstantRadius (d : ℕ) : ℝ := 10 / (d : ℝ) ^ 3

def sourceT1 (n d L : ℕ) : Set (Fin n → ℂ) :=
  {x | x ∉ sourceT0 n d L ∧ x ∉ sourceT3 n d L ∧
    Real.rpow (d : ℝ) (3 / 2) * orderedNormAt x (secondSteepScale n d) <
      orderedNormAt x (firstSteepScale n d)}

def sourceT2 (n d L : ℕ) (a₃ : ℝ) : Set (Fin n → ℂ) :=
  {x | x ∉ sourceT0 n d L ∧ x ∉ sourceT1 n d L ∧ x ∉ sourceT3 n d L ∧
    Real.rpow (d : ℝ) (3 / 2) * orderedNormAt x (thirdSteepScale n a₃) <
      orderedNormAt x (secondSteepScale n d)}

def sourceSteepUnion (n d L : ℕ) (a₃ : ℝ) : Set (Fin n → ℂ) :=
  sourceT0 n d L ∪ sourceT1 n d L ∪ sourceT2 n d L a₃ ∪ sourceT3 n d L

def sourceShiftedSteepUnion (n d L : ℕ) (a₃ : ℝ) : Set (Fin n → ℂ) :=
  {v | ∃ (x : Fin n → ℂ) (c : ℂ), x ∈ sourceSteepUnion n d L a₃ ∧
    ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10 ∧ v = fun j => x j + c}

def sourceShiftedT1 (n d L : ℕ) : Set (Fin n → ℂ) :=
  {v | ∃ (x : Fin n → ℂ) (c : ℂ), x ∈ sourceT1 n d L ∧
    ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10 ∧ v = fun j => x j + c}

def sourceShiftedT2 (n d L : ℕ) (a₃ : ℝ) : Set (Fin n → ℂ) :=
  {v | ∃ (x : Fin n → ℂ) (c : ℂ), x ∈ sourceT2 n d L a₃ ∧
    ‖c‖ ≤ orderedNormAt x (firstSteepScale n d) / 10 ∧ v = fun j => x j + c}

theorem sourceShiftedSteepUnion_eq (n d L : ℕ) (a₃ : ℝ) :
    sourceShiftedSteepUnion n d L a₃ = sourceShiftedT0 n d L ∪ sourceShiftedT1 n d L ∪
      sourceShiftedT2 n d L a₃ ∪ sourceShiftedT3 n d L := by
  ext v
  constructor
  · rintro ⟨x, c, ((h0 | h1) | h2) | h3, hCenter, hEq⟩
    · exact Or.inl (Or.inl (Or.inl ⟨x, c, h0, hCenter, hEq⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨x, c, h1, hCenter, hEq⟩))
    · exact Or.inl (Or.inr ⟨x, c, h2, hCenter, hEq⟩)
    · exact Or.inr ⟨x, c, h3, hCenter, hEq⟩
  · rintro (((⟨x, c, h0, hCenter, hEq⟩ | ⟨x, c, h1, hCenter, hEq⟩) |
      ⟨x, c, h2, hCenter, hEq⟩) | ⟨x, c, h3, hCenter, hEq⟩)
    · exact ⟨x, c, Or.inl (Or.inl (Or.inl h0)), hCenter, hEq⟩
    · exact ⟨x, c, Or.inl (Or.inl (Or.inr h1)), hCenter, hEq⟩
    · exact ⟨x, c, Or.inl (Or.inr h2), hCenter, hEq⟩
    · exact ⟨x, c, Or.inr h3, hCenter, hEq⟩

def almostConstantCoordinates {n : ℕ} (x : Fin n → ℂ) (k : ℕ) (θ : ℝ) (c : ℂ) :
    Finset (Fin n) := Finset.univ.filter (fun j => ‖x j - c‖ ≤ θ * orderedNormAt x k)

def sourceAlmostConstant (n d : ℕ) (a₃ : ℝ) : Set (Fin n → ℂ) :=
  {x | ∃ c : ℂ, n - thirdSteepScale n a₃ <
    (almostConstantCoordinates x (thirdSteepScale n a₃) (almostConstantRadius d) c).card}

def sourceS (n d : ℕ) (a₃ t : ℝ) : Set (Fin n → ℂ) :=
  {x | 0 < orderedNormAt x (almostConstantRank n d) ∧
    orderedNormAt x (almostConstantRank n d) ≤ t * orderedNormAt x (thirdSteepScale n a₃)}

theorem degree_three_halves_sq {d : ℕ} (hd : 0 < d) :
    Real.rpow (d : ℝ) (3 / 2) ^ 2 = (d : ℝ) ^ 3 := by
  rw [degree_three_halves_eq hd]
  calc
    _ = (d : ℝ) ^ 2 * Real.sqrt d ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg d)]; ring

theorem source_steep_union_of_large_gap {n d L : ℕ} (hd : 0 < d) (a₃ : ℝ)
    (x : Fin n → ℂ)
    (hGap : (d : ℝ) ^ 3 * orderedNormAt x (thirdSteepScale n a₃) <
      orderedNormAt x (firstSteepScale n d)) : x ∈ sourceSteepUnion n d L a₃ := by
  by_cases h0 : x ∈ sourceT0 n d L
  · exact Or.inl (Or.inl (Or.inl h0))
  by_cases h3 : x ∈ sourceT3 n d L
  · exact Or.inr h3
  by_cases h1 : x ∈ sourceT1 n d L
  · exact Or.inl (Or.inl (Or.inr h1))
  have hBound1 : orderedNormAt x (firstSteepScale n d) ≤
      Real.rpow (d : ℝ) (3 / 2) * orderedNormAt x (secondSteepScale n d) := by
    apply le_of_not_gt
    intro h
    exact h1 ⟨h0, h3, h⟩
  have hJump2 : Real.rpow (d : ℝ) (3 / 2) * orderedNormAt x (thirdSteepScale n a₃) <
      orderedNormAt x (secondSteepScale n d) := by
    by_contra h
    have hBound2 := le_of_not_gt h
    have hScale := Real.rpow_nonneg (Nat.cast_nonneg d) (3 / 2 : ℝ)
    have hScaled := mul_le_mul_of_nonneg_left hBound2 hScale
    have hCombined : orderedNormAt x (firstSteepScale n d) ≤
        (d : ℝ) ^ 3 * orderedNormAt x (thirdSteepScale n a₃) := by
      calc
        _ ≤ Real.rpow (d : ℝ) (3 / 2) * orderedNormAt x (secondSteepScale n d) := hBound1
        _ ≤ Real.rpow (d : ℝ) (3 / 2) *
            (Real.rpow (d : ℝ) (3 / 2) * orderedNormAt x (thirdSteepScale n a₃)) := hScaled
        _ = _ := by rw [← mul_assoc, ← pow_two, degree_three_halves_sq hd]
    exact (not_lt_of_ge hCombined) hGap
  exact Or.inl (Or.inr ⟨h0, h1, h3, hJump2⟩)

end CircularLaw
