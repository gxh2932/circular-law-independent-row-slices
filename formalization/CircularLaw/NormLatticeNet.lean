import CircularLaw.NormLatticeRounding

/-!
# A constructed Euclidean unit-ball net of size at most `128^n`

The finite net is the literal image of the bounded integer vectors,
rescaled by `9*sqrt(n)`. Coordinate rounding constructs a member for
every vector in the unit ball. Every net point remains in that ball,
and the approximation distance is at most `1/4`.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def normLatticeRadius (n : ℕ) : ℕ := ⌈9 * Real.sqrt n⌉₊

def normLatticePoint {n R : ℕ} (q : NormLatticeBox n R) : EuclideanSpace ℝ (Fin n) :=
  (1 / (9 * Real.sqrt n)) • WithLp.toLp 2 (fun i => (q i).val : Fin n → ℝ)

def normLatticeNet (n : ℕ) : Finset (EuclideanSpace ℝ (Fin n)) :=
  (normBoundedLattice n (normLatticeRadius n)).image normLatticePoint

theorem normLatticePoint_norm_bound {n R : ℕ} (hn : 0 < n) {q : NormLatticeBox n R}
    (hq : q ∈ normBoundedLattice n R) : ‖normLatticePoint q‖ ≤ 1 := by
  have hRoot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hMass : normLatticeSquaredMass q ≤ 81 * (n : ℝ) := (Finset.mem_filter.mp hq).2
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => ((q i).val : ℝ))
  have hNormSq : ‖v‖ ^ 2 = normLatticeSquaredMass q := real_euclidean_norm_sq v
  have hRootSq := Real.sq_sqrt (Nat.cast_nonneg n)
  have hNorm : ‖v‖ ≤ 9 * Real.sqrt n := by
    nlinarith [norm_nonneg v, Real.sqrt_nonneg (n : ℝ)]
  change ‖(1 / (9 * Real.sqrt n)) • v‖ ≤ 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (1 / (9 * Real.sqrt n)) * (9 * Real.sqrt n) := mul_le_mul_of_nonneg_left hNorm (by positivity)
    _ = _ := by field_simp

theorem normLatticeNet_card_le (n : ℕ) : (normLatticeNet n).card ≤ 128 ^ n :=
  Finset.card_image_le.trans (normBoundedLattice_card_le n (normLatticeRadius n))

theorem normLatticeNet_norm_bound {n : ℕ} (hn : 0 < n) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ normLatticeNet n) : ‖z‖ ≤ 1 := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
  exact normLatticePoint_norm_bound hn hq

theorem normRoundInteger_abs_bound {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (i : Fin n) :
    |(normRoundInteger x i : ℝ)| ≤ 9 * Real.sqrt n := by
  have hCoordinate : (normRoundInteger x i : ℝ) ^ 2 ≤ ∑ j, (normRoundInteger x j : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin n => (normRoundInteger x j : ℝ) ^ 2)
      (fun j _ => sq_nonneg (normRoundInteger x j : ℝ)) (Finset.mem_univ i)
  have hMass := normRoundInteger_squared_mass x hx
  have hRoot := Real.sq_sqrt (Nat.cast_nonneg n)
  have hAbs := sq_abs (normRoundInteger x i : ℝ)
  nlinarith [abs_nonneg (normRoundInteger x i : ℝ), Real.sqrt_nonneg (n : ℝ)]

theorem normRoundInteger_mem_box {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (i : Fin n) :
    normRoundInteger x i ∈ Finset.Icc (-(normLatticeRadius n : ℤ)) (normLatticeRadius n : ℤ) := by
  have hRadius : 9 * Real.sqrt n ≤ (normLatticeRadius n : ℝ) := Nat.le_ceil _
  have hAbs := (normRoundInteger_abs_bound x hx i).trans hRadius
  have hBounds := abs_le.mp hAbs
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast hBounds.1
  · exact_mod_cast hBounds.2

def normRoundBox {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) :
    NormLatticeBox n (normLatticeRadius n) :=
  fun i => ⟨normRoundInteger x i, normRoundInteger_mem_box x hx i⟩

theorem normRoundBox_mem_bounded {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) :
    normRoundBox x hx ∈ normBoundedLattice n (normLatticeRadius n) := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, normRoundInteger_squared_mass x hx⟩

theorem normRoundBox_point {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) :
    normLatticePoint (normRoundBox x hx) = normRoundPoint x := rfl

theorem normRoundPoint_mem_net {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) :
    normRoundPoint x ∈ normLatticeNet n := by
  apply Finset.mem_image.mpr
  exact ⟨normRoundBox x hx, normRoundBox_mem_bounded x hx, normRoundBox_point x hx⟩

theorem normLatticeNet_unit_ball_cover {n : ℕ} (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) :
    ∃ z ∈ normLatticeNet n, ‖x - z‖ ≤ 1 / 4 :=
  ⟨normRoundPoint x, normRoundPoint_mem_net x hx, normRoundPoint_distance_bound hn x hx⟩

end CircularLaw
