import CircularLaw.NormLatticeNet
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# An exponential-size half-net of the complex Euclidean ball

The real and imaginary parts use the actual real lattice quarter-net.
Their joint image has at most `128^(2*n)` points, each of norm at most
two, and covers the complex unit ball within distance one half.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def realEuclideanToComplex {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun i => (x i : ℂ))

def complexEuclideanRe {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => (x i).re)

def complexEuclideanIm {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => (x i).im)

theorem real_euclidean_to_complex_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖realEuclideanToComplex x‖ = ‖x‖ := by
  have h : ‖realEuclideanToComplex x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun t : ℝ => t ^ 2) (Complex.norm_real (x i))
  nlinarith [norm_nonneg (realEuclideanToComplex x), norm_nonneg x]

theorem real_euclidean_to_complex_sub {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    realEuclideanToComplex (x - y) = realEuclideanToComplex x - realEuclideanToComplex y := by
  ext i
  exact Complex.ofReal_sub (x i) (y i)

theorem complex_euclidean_re_norm_le {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) :
    ‖complexEuclideanRe x‖ ≤ ‖x‖ := by
  have h : ‖complexEuclideanRe x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using Complex.abs_re_le_norm (x i)) 2
  nlinarith [norm_nonneg (complexEuclideanRe x), norm_nonneg x]

theorem complex_euclidean_im_norm_le {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) :
    ‖complexEuclideanIm x‖ ≤ ‖x‖ := by
  have h : ‖complexEuclideanIm x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using Complex.abs_im_le_norm (x i)) 2
  nlinarith [norm_nonneg (complexEuclideanIm x), norm_nonneg x]

theorem complex_euclidean_re_im_decomposition {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) :
    x = realEuclideanToComplex (complexEuclideanRe x) +
      Complex.I • realEuclideanToComplex (complexEuclideanIm x) := by
  ext i
  change x i = (x i).re + Complex.I * (x i).im
  simpa only [mul_comm] using (Complex.re_add_im (x i)).symm

def complexHalfLatticeNet (n : ℕ) : Finset (EuclideanSpace ℂ (Fin n)) :=
  ((normLatticeNet n) ×ˢ (normLatticeNet n)).image
    (fun p => realEuclideanToComplex p.1 + Complex.I • realEuclideanToComplex p.2)

theorem complex_half_lattice_net_card_le (n : ℕ) :
    (complexHalfLatticeNet n).card ≤ 128 ^ (2 * n) := by
  apply Finset.card_image_le.trans
  rw [Finset.card_product]
  calc
    _ ≤ 128 ^ n * 128 ^ n := Nat.mul_le_mul (normLatticeNet_card_le n) (normLatticeNet_card_le n)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem complex_half_lattice_net_card_exponential (n : ℕ) :
    ((complexHalfLatticeNet n).card : ℝ) ≤ Real.exp (14 * (n : ℝ)) := by
  have hTwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at h
    exact h.le
  calc
    _ ≤ (128 : ℝ) ^ (2 * n) := by exact_mod_cast complex_half_lattice_net_card_le n
    _ = ((2 : ℝ) ^ 7) ^ (2 * n) := by norm_num
    _ ≤ ((Real.exp 1) ^ 7) ^ (2 * n) :=
      pow_le_pow_left₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) hTwo 7) (2 * n)
    _ = _ := by rw [← pow_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem complex_half_lattice_net_norm_le {n : ℕ} (hn : 0 < n)
    {u : EuclideanSpace ℂ (Fin n)} (hu : u ∈ complexHalfLatticeNet n) : ‖u‖ ≤ 2 := by
  obtain ⟨⟨v, w⟩, hvw, rfl⟩ := Finset.mem_image.mp hu
  have hv := normLatticeNet_norm_bound hn (Finset.mem_product.mp hvw).1
  have hw := normLatticeNet_norm_bound hn (Finset.mem_product.mp hvw).2
  calc
    _ ≤ ‖realEuclideanToComplex v‖ + ‖Complex.I • realEuclideanToComplex w‖ := norm_add_le _ _
    _ = ‖v‖ + ‖w‖ := by rw [norm_smul, Complex.norm_I, one_mul,
      real_euclidean_to_complex_norm, real_euclidean_to_complex_norm]
    _ ≤ _ := by linarith

theorem complex_half_lattice_net_cover {n : ℕ} (hn : 0 < n)
    (x : EuclideanSpace ℂ (Fin n)) (hx : ‖x‖ ≤ 1) :
    ∃ u ∈ complexHalfLatticeNet n, ‖x - u‖ ≤ 1 / 2 := by
  obtain ⟨v, hv, hCloseV⟩ := normLatticeNet_unit_ball_cover hn (complexEuclideanRe x)
    ((complex_euclidean_re_norm_le x).trans hx)
  obtain ⟨w, hw, hCloseW⟩ := normLatticeNet_unit_ball_cover hn (complexEuclideanIm x)
    ((complex_euclidean_im_norm_le x).trans hx)
  refine ⟨realEuclideanToComplex v + Complex.I • realEuclideanToComplex w,
    Finset.mem_image.mpr ⟨(v, w), Finset.mem_product.mpr ⟨hv, hw⟩, rfl⟩, ?_⟩
  have hEq : x - (realEuclideanToComplex v + Complex.I • realEuclideanToComplex w) =
      realEuclideanToComplex (complexEuclideanRe x - v) +
        Complex.I • realEuclideanToComplex (complexEuclideanIm x - w) := by
    rw [real_euclidean_to_complex_sub, real_euclidean_to_complex_sub, smul_sub]
    nth_rw 1 [complex_euclidean_re_im_decomposition x]
    abel
  rw [hEq]
  calc
    _ ≤ ‖realEuclideanToComplex (complexEuclideanRe x - v)‖ +
        ‖Complex.I • realEuclideanToComplex (complexEuclideanIm x - w)‖ := norm_add_le _ _
    _ = ‖complexEuclideanRe x - v‖ + ‖complexEuclideanIm x - w‖ := by
      rw [norm_smul, Complex.norm_I, one_mul, real_euclidean_to_complex_norm,
        real_euclidean_to_complex_norm]
    _ ≤ _ := by linarith

end CircularLaw
