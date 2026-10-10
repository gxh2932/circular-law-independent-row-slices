import CircularLaw.SchurEigenvalueEnergy

/-!
# A first eigenvalue moment bounded by the Hilbert--Schmidt energy

Cauchy--Schwarz is applied to a full enumeration of the characteristic
root multiset, so repeated roots retain their algebraic multiplicity.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

theorem multiset_map_sum_eq_fin_sum {α : Type*} (s : Multiset α) (f : α → ℝ) :
    (s.map f).sum = ∑ i : Fin s.toList.length, f (s.toList.get i) := by
  have hFn : List.ofFn (fun i => f (s.toList.get i)) = s.toList.map f := by
    change List.ofFn (f ∘ s.toList.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [← Multiset.sum_map_toList s f, ← hFn, List.sum_ofFn]

theorem multiset_sum_sq_le_card_mul_sum_sq (s : Multiset ℝ) :
    s.sum ^ 2 ≤ (s.card : ℝ) * (s.map (fun x => x ^ 2)).sum := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin s.toList.length => s.toList.get i) (fun _ => (1 : ℝ))
  have hSum : s.sum = ∑ i : Fin s.toList.length, s.toList.get i := by
    have h := multiset_map_sum_eq_fin_sum s (fun x : ℝ => x)
    rw [Multiset.map_id'] at h
    exact h
  have hSquare := multiset_map_sum_eq_fin_sum s (fun x => x ^ 2)
  simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Multiset.length_toList, ← hSum, ← hSquare, mul_comm] using hCS

def squareEigenvalueFirstMoment {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (A.charpoly.roots.map (fun z => ‖z‖)).sum / n

theorem square_eigenvalue_first_moment_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ squareEigenvalueFirstMoment A := by
  apply div_nonneg
  · exact Multiset.sum_nonneg (fun _ h => by
      obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp h
      exact norm_nonneg z)
  · exact Nat.cast_nonneg _

theorem square_eigenvalue_first_moment_sq_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    squareEigenvalueFirstMoment A ^ 2 ≤ squareMatrixEnergy A / n := by
  have hCS := multiset_sum_sq_le_card_mul_sum_sq (A.charpoly.roots.map (fun z => ‖z‖))
  have hCard : A.charpoly.roots.card = n := by
    rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots]
    simp
  simp only [Multiset.card_map, Multiset.map_map, Function.comp_apply, hCard] at hCS
  have hSchur := square_eigenvalue_energy_le A
  by_cases hn : n = 0
  · simp [squareEigenvalueFirstMoment, hn]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [squareEigenvalueFirstMoment, div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hnR)).mpr
    have hBound : (A.charpoly.roots.map (fun z => ‖z‖)).sum ^ 2 ≤
        (n : ℝ) * squareMatrixEnergy A :=
      hCS.trans (mul_le_mul_of_nonneg_left hSchur hnR.le)
    have hEq : squareMatrixEnergy A / n * (n : ℝ) ^ 2 = (n : ℝ) * squareMatrixEnergy A := by
      field_simp
    rw [hEq]
    exact hBound

theorem square_eigenvalue_first_moment_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    squareEigenvalueFirstMoment A ≤ Real.sqrt (squareMatrixEnergy A / n) := by
  have hSq := square_eigenvalue_first_moment_sq_bound A
  have hEnergy := div_nonneg (squareMatrixEnergy_nonneg A) (Nat.cast_nonneg n)
  have hRoot := Real.sq_sqrt hEnergy
  have hRootNonneg := Real.sqrt_nonneg (squareMatrixEnergy A / n)
  nlinarith

end CircularLaw
