import CircularLaw.WitnessSelection

/-!
# Equal-block norm bounds on the actual matrix exposure

Expose each row's singleton mask and fixed support. The joint exposure
fiber is the product of these exact row-slice fibers. Selected rows inherit
the one-half bound or the Esseen bound according to their witness counts.
The coefficient vector, constant vector and diagonal shift are literal
row actions, with no extra independence assumption.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def singletonMatrixExposure {n d : ℕ} {ι κ : Type*}
    [Fintype κ] [DecidableEq κ] (J : κ → Finset (Fin n)) (rows : ι → RowSlice n d) :=
  fun i => singletonExposure J (rows i)

def shiftedRowAction {n d : ℕ} (S : RowSlice n d) (y : Fin n → ℂ)
    (c ζ : ℂ) (i : Fin n) : ℂ :=
  rowLinearForm S (fun j => y j + c) - ζ * (y i + c)

theorem singleton_exposure_shifted_row_bound {n d : ℕ} {κ : Type*}
    [Fintype κ] [DecidableEq κ] (J : κ → Finset (Fin n))
    (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (reference : RowSlice n d) (hb : 1 ≤ (singletonWitnessMask J reference).card)
    (y : Fin n → ℂ) {r : ℝ} (hr : 0 < r)
    (hAtom : ∀ q z, uniformProbability (fun j : {j : Fin n // j ∈ J q} =>
      ‖y j.val - z‖ ≤ r) ≤ 1 / 2) (c ζ : ℂ) (i : Fin n) :
    uniformProbability (fun S : {S : RowSlice n d //
      singletonExposure J S = singletonExposure J reference} =>
      ‖shiftedRowAction S.val y c ζ i‖ < r) ≤
        min (1 / 2) ((2 * (24 * Real.exp 1 / Real.pi)) /
          Real.sqrt ((singletonWitnessMask J reference).card : ℝ)) := by
  have h := singleton_exposure_conditional_small_ball J hDis reference hb y hr hAtom
    ((d : ℂ) * c - ζ * (y i + c)) 0
  apply (uniformProbability_mono ?_).trans h
  intro S hS
  simpa only [shiftedRowAction, shifted_row_action_eq_center, sub_zero] using hS.le

theorem equal_block_exposure_norm_half {n d : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (J : κ → Finset (Fin n)) (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (reference : ι → RowSlice n d) (I : Finset ι)
    (hb : ∀ i ∈ I, 1 ≤ (singletonWitnessMask J (reference i)).card)
    (y : Fin n → ℂ) {r : ℝ} (hr : 0 < r)
    (hAtom : ∀ q z, uniformProbability (fun j : {j : Fin n // j ∈ J q} =>
      ‖y j.val - z‖ ≤ r) ≤ 1 / 2) (c ζ : ℂ) (index : ι → Fin n) :
    uniformProbability (fun rows : {rows : ι → RowSlice n d //
      singletonMatrixExposure J rows = singletonMatrixExposure J reference} =>
      (∑ i : I, ‖shiftedRowAction (rows.val i.val) y c ζ (index i.val)‖ ^ 2) ≤
        r ^ 2 * (I.card : ℝ) / 8) ≤ Real.exp (-witnessHalfRate * I.card) := by
  apply product_fiber_subset_norm_small_ball_half (fun _ => singletonExposure J) reference I
    (fun i S => shiftedRowAction S y c ζ (index i)) hr
  intro i hi
  exact (singleton_exposure_shifted_row_bound J hDis (reference i) (hb i hi)
    y hr hAtom c ζ (index i)).trans (min_le_left _ _)

theorem equal_block_exposure_norm_log {n d : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (J : κ → Finset (Fin n)) (hDis : Pairwise (fun q p => Disjoint (J q) (J p)))
    (reference : ι → RowSlice n d) (I : Finset ι)
    (hb : ∀ i ∈ I, 1 ≤ (singletonWitnessMask J (reference i)).card)
    (y : Fin n → ℂ) {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hpHalf : p ≤ 1 / 2)
    (hAtom : ∀ q z, uniformProbability (fun j : {j : Fin n // j ∈ J q} =>
      ‖y j.val - z‖ ≤ r) ≤ 1 / 2)
    (hEsseen : ∀ i ∈ I, (2 * (24 * Real.exp 1 / Real.pi)) /
      Real.sqrt ((singletonWitnessMask J (reference i)).card : ℝ) ≤ p)
    (c ζ : ℂ) (index : ι → Fin n) :
    uniformProbability (fun rows : {rows : ι → RowSlice n d //
      singletonMatrixExposure J rows = singletonMatrixExposure J reference} =>
      (∑ i : I, ‖shiftedRowAction (rows.val i.val) y c ζ (index i.val)‖ ^ 2) ≤
        r ^ 2 * (I.card : ℝ) / 8) ≤
      Real.exp (-witnessLogRate * I.card * Real.log (1 / p)) := by
  apply product_fiber_subset_norm_small_ball_log (fun _ => singletonExposure J) reference I
    (fun i S => shiftedRowAction S y c ζ (index i)) hr hp hpHalf
  intro i hi
  exact (singleton_exposure_shifted_row_bound J hDis (reference i) (hb i hi)
    y hr hAtom c ζ (index i)).trans ((min_le_right _ _).trans (hEsseen i hi))

end CircularLaw
