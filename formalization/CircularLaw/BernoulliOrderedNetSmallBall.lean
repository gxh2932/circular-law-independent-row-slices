import CircularLaw.BernoulliRetainedSmallBall
import Mathlib.MeasureTheory.Measure.Real

/-!
# Bernoulli fixed-vector decay and finite-net unions from ordered gaps

The rare bound keeps enough retained rows for the manuscript's 1/30 norm
radius. The large bound uses tensorization at scale sqrt(2), so it also
covers every retained set containing at least half the rows.
-/

noncomputable section
open Classical MeasureTheory
open scoped BigOperators

namespace CircularLaw

theorem bernoulli_retained_ordered_rare_norm_decay {n d rank tail : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) (hRank : 0 < rank) (hFit : tail + rank ≤ n)
    (I : Finset (Fin n)) (hRows : (4 / 5 : ℝ) * n ≤ I.card)
    (hRare : (rank : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (y : Fin n → ℂ) (c ζ : ℂ)
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      2 / 3 + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
        (WithLp.toLp 2 (fun j => y j + c))‖ ≤ Real.sqrt ((rank : ℝ) * d) / 30} ≤
      Real.exp (-(rank : ℝ) * d / 16) := by
  let q := (rank : ℝ) * ((d : ℝ) / n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hCancel : q * n = (rank : ℝ) * d := by dsimp [q]; field_simp
  have hDensity : (4 / 5 : ℝ) * ((rank : ℝ) * d) ≤ q * I.card := by
    have h := mul_le_mul_of_nonneg_left hRows hq
    nlinarith only [h, hCancel]
  have hSub : {sample : BernoulliSquareSample n |
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
        (WithLp.toLp 2 (fun j => y j + c))‖ ≤ Real.sqrt ((rank : ℝ) * d) / 30} ⊆
      {sample | ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
        (WithLp.toLp 2 (fun j => y j + c))‖ ^ 2 ≤ (1 / 3 : ℝ) ^ 2 * q * I.card / 72} := by
    intro sample hSmall
    have hSquare := pow_le_pow_left₀ (norm_nonneg _) hSmall 2
    rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ (rank : ℝ) * d)] at hSquare
    change ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
      (WithLp.toLp 2 (fun j => y j + c))‖ ^ 2 ≤ (1 / 3 : ℝ) ^ 2 * q * I.card / 72
    nlinarith only [hSquare, hDensity,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) rank) (Nat.cast_nonneg (α := ℝ) d)]
  apply (measureReal_mono hSub (h₂ := by finiteness)).trans
  apply (bernoulli_retained_ordered_rare_small_ball hn hdn hRank hFit I hRare y c ζ
    (by norm_num : (0 : ℝ) < 1 / 3) (by simpa only [show (2 : ℝ) * (1 / 3) = 2 / 3 by ring] using hGap)).trans
  apply Real.exp_le_exp.mpr
  change -q * I.card / 8 ≤ _
  nlinarith only [hDensity,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) rank) (Nat.cast_nonneg (α := ℝ) d)]

theorem bernoulli_retained_ordered_large_norm_small_ball {n d rank tail : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hRank : 0 < rank) (hFit : tail + rank ≤ n)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card)
    (y : Fin n → ℂ) (c ζ : ℂ)
    (hGap : ∀ j : Fin n, tail ≤ j.val →
      2 / 3 + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
        (WithLp.toLp 2 (fun j => y j + c))‖ ≤ Real.sqrt n / 3} ≤
      (8 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
        Real.sqrt ((rank : ℝ) * ((d : ℝ) / n)))) ^ I.card := by
  have hRoot : (1 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hBound := bernoulli_retained_ordered_large_small_ball hd hDegree hRank hFit I y c ζ
    (by norm_num : (0 : ℝ) < 1 / 3) hRoot
    (by simpa only [show (2 : ℝ) * (1 / 3) = 2 / 3 by ring] using hGap)
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hBound
  apply (measureReal_mono (μ := sparseBernoulliMatrixLaw n d) ?_ (h₂ := by finiteness)).trans
    (hBound.trans_eq ?_)
  · intro sample hSmall
    have hSquare := pow_le_pow_left₀ (norm_nonneg _) hSmall 2
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at hSquare
    change ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
      (WithLp.toLp 2 (fun j => y j + c))‖ ^ 2 ≤ 2 * (1 / 3 : ℝ) ^ 2 * I.card
    nlinarith only [hSquare, hRows]
  · congr 1
    ring

theorem finite_probability_finset_exists_le {Ω α : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Finset α) (E : α → Ω → Prop) :
    μ.real {ω | ∃ a ∈ S, E a ω} ≤ ∑ a ∈ S, μ.real {ω | E a ω} := by
  have hEvent : {ω | ∃ a ∈ S, E a ω} = ⋃ a ∈ S, {ω | E a ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [hEvent]
  exact measureReal_biUnion_finset_le S _

theorem bernoulli_ordered_rare_net_union_probability {n d rank tail : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) (hRank : 0 < rank) (hFit : tail + rank ≤ n)
    (I : Finset (Fin n)) (hRows : (4 / 5 : ℝ) * n ≤ I.card)
    (hRare : (rank : ℝ) * ((d : ℝ) / n) ≤ 1 / 2)
    (N : Finset (Fin n → ℂ))
    (hGap : ∀ y ∈ N, ∀ j : Fin n, tail ≤ j.val →
      2 / 3 + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩)
    (C : Finset ℂ) (ζ : ℂ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ∃ y ∈ N, ∃ c ∈ C,
        ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
          (WithLp.toLp 2 (fun j => y j + c))‖ ≤ Real.sqrt ((rank : ℝ) * d) / 30} ≤
      (N.card : ℝ) * C.card * Real.exp (-(rank : ℝ) * d / 16) := by
  apply (finite_probability_finset_exists_le _ N _).trans
  calc
    _ ≤ ∑ _y ∈ N, (C.card : ℝ) * Real.exp (-(rank : ℝ) * d / 16) := by
      apply Finset.sum_le_sum
      intro y hy
      apply (finite_probability_finset_exists_le _ C _).trans
      calc
        _ ≤ ∑ _c ∈ C, Real.exp (-(rank : ℝ) * d / 16) :=
          Finset.sum_le_sum (fun c _ => bernoulli_retained_ordered_rare_norm_decay
            hn hdn hRank hFit I hRows hRare y c ζ (hGap y hy))
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem bernoulli_ordered_large_net_union_probability {n d rank tail : ℕ}
    (hd : 0 < d) (hDegree : 2 * d ≤ n) (hRank : 0 < rank) (hFit : tail + rank ≤ n)
    (I : Finset (Fin n)) (hRows : (n : ℝ) / 2 ≤ I.card)
    (N : Finset (Fin n → ℂ))
    (hGap : ∀ y ∈ N, ∀ j : Fin n, tail ≤ j.val →
      2 / 3 + orderedNorm y j < orderedNorm y ⟨rank - 1, by omega⟩)
    (C : Finset ℂ) (ζ : ℂ) :
    (sparseBernoulliMatrixLaw n d).real {sample |
      ∃ y ∈ N, ∃ c ∈ C,
        ‖(retainedShiftedBernoulliMatrix I ζ sample).toEuclideanLin
          (WithLp.toLp 2 (fun j => y j + c))‖ ≤ Real.sqrt n / 3} ≤
      (N.card : ℝ) * C.card * (8 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
        Real.sqrt ((rank : ℝ) * ((d : ℝ) / n)))) ^ I.card := by
  apply (finite_probability_finset_exists_le _ N _).trans
  calc
    _ ≤ ∑ _y ∈ N, (C.card : ℝ) * (8 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
        Real.sqrt ((rank : ℝ) * ((d : ℝ) / n)))) ^ I.card := by
      apply Finset.sum_le_sum
      intro y hy
      apply (finite_probability_finset_exists_le _ C _).trans
      calc
        _ ≤ ∑ _c ∈ C, (8 * Real.exp 1 * (bernoulliScalarSmallBallConstant /
            Real.sqrt ((rank : ℝ) * ((d : ℝ) / n)))) ^ I.card :=
          Finset.sum_le_sum (fun c _ => bernoulli_retained_ordered_large_norm_small_ball
            hd hDegree hRank hFit I hRows y c ζ (hGap y hy))
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end CircularLaw
