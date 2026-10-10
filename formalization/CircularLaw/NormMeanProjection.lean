import CircularLaw.NormLatticeNet
import CircularLaw.FiniteMean

/-!
# Mean removal and an actual net inside the zero-sum unit ball

Subtracting the coordinate mean decreases the Euclidean norm. The image
of the constructed lattice net under this projection is therefore still
inside the unit ball and covers its zero-sum subspace at the same radius.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def normMeanProjection {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => x i - finiteMean (fun j => x j))

theorem normMeanProjection_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    normMeanProjection x i = x i - finiteMean (fun j => x j) := rfl

theorem coordinate_sum_eq_card_mean {n : ℕ} (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, x i = (n : ℝ) * finiteMean (fun j => x j) := by
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [finiteMean, Fintype.card_fin]
  field_simp

theorem normMeanProjection_sum_zero {n : ℕ} (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, normMeanProjection x i = 0 := by
  simp only [normMeanProjection_apply, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [coordinate_sum_eq_card_mean hn x, sub_self]

theorem normMeanProjection_sub {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    normMeanProjection (x - y) = normMeanProjection x - normMeanProjection y := by
  apply WithLp.ofLp_injective
  funext i
  simp only [normMeanProjection, WithLp.ofLp_toLp, WithLp.ofLp_sub, Pi.sub_apply,
    finiteMean_sub]
  ring

theorem normMeanProjection_eq_of_sum_zero {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : ∑ i, x i = 0) : normMeanProjection x = x := by
  have hMean : finiteMean (fun j => x j) = 0 := by simp [finiteMean, hx]
  apply WithLp.ofLp_injective
  funext i
  simp [normMeanProjection, hMean]

theorem normMeanProjection_variance_identity {n : ℕ} (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖normMeanProjection x‖ ^ 2 + (n : ℝ) * (finiteMean (fun j => x j)) ^ 2 = ‖x‖ ^ 2 := by
  rw [real_euclidean_norm_sq, real_euclidean_norm_sq]
  simp only [normMeanProjection_apply]
  have hExpand : ∑ i, (x i - finiteMean (fun j => x j)) ^ 2 =
      (∑ i, (x i) ^ 2) - 2 * finiteMean (fun j => x j) * (∑ i, x i) +
        (n : ℝ) * (finiteMean (fun j => x j)) ^ 2 := by
    calc
      _ = ∑ i, ((x i) ^ 2 - 2 * finiteMean (fun j => x j) * x i +
          (finiteMean (fun j => x j)) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hExpand, coordinate_sum_eq_card_mean hn x]
  ring

theorem normMeanProjection_norm_le {n : ℕ} (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖normMeanProjection x‖ ≤ ‖x‖ := by
  have h := normMeanProjection_variance_identity hn x
  have hNonneg : 0 ≤ (n : ℝ) * (finiteMean (fun j => x j)) ^ 2 := by positivity
  nlinarith [norm_nonneg (normMeanProjection x), norm_nonneg x]

def normZeroMeanNet (n : ℕ) : Finset (EuclideanSpace ℝ (Fin n)) :=
  (normLatticeNet n).image normMeanProjection

theorem normZeroMeanNet_card_le (n : ℕ) : (normZeroMeanNet n).card ≤ 128 ^ n :=
  Finset.card_image_le.trans (normLatticeNet_card_le n)

theorem normZeroMeanNet_norm_bound {n : ℕ} (hn : 0 < n) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ normZeroMeanNet n) : ‖z‖ ≤ 1 := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  exact (normMeanProjection_norm_le hn x).trans (normLatticeNet_norm_bound hn hx)

theorem normZeroMeanNet_sum_zero {n : ℕ} (hn : 0 < n) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ normZeroMeanNet n) : ∑ i, z i = 0 := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  exact normMeanProjection_sum_zero hn x

theorem normZeroMeanNet_unit_ball_cover {n : ℕ} (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hSum : ∑ i, x i = 0) :
    ∃ z ∈ normZeroMeanNet n, ‖x - z‖ ≤ 1 / 4 := by
  obtain ⟨y, hy, hClose⟩ := normLatticeNet_unit_ball_cover hn x hx
  refine ⟨normMeanProjection y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
  have hIdentity : x - normMeanProjection y = normMeanProjection (x - y) := by
    rw [normMeanProjection_sub, normMeanProjection_eq_of_sum_zero x hSum]
  rw [hIdentity]
  exact (normMeanProjection_norm_le hn (x - y)).trans hClose

end CircularLaw
