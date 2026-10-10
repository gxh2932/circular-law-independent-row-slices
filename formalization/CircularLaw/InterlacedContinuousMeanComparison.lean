import CircularLaw.ClippedInterlacingMeanBounds
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Bounded continuous means under one-index interlacing

Uniform continuity controls clipped values, whose mean distance is at
most twice the cutoff divided by dimension. The unclipped error is
supported on the upper tails. Interlacing bounds one array's tail
fraction by the other's plus one over dimension.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal

namespace CircularLaw

theorem finite_above_fraction_eq_below_complement {n : ℕ} (hn : 0 < n)
    (s : Fin n → ℝ) (S : ℝ) :
    finiteMean (fun i => if S ≤ s i then (1 : ℝ) else 0) =
      1 - (finiteBelowCount s S : ℝ) / n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hPoint : (fun i => (if S ≤ s i then (1 : ℝ) else 0) +
      (if s i < S then (1 : ℝ) else 0)) = fun _ => (1 : ℝ) := by
    funext i
    split_ifs <;> linarith
  have hSum : finiteMean (fun i => if S ≤ s i then (1 : ℝ) else 0) +
      finiteMean (fun i => if s i < S then (1 : ℝ) else 0) = 1 := by
    rw [← finiteMean_add, hPoint, finiteMean_const]
  have hBelow : finiteMean (fun i => if s i < S then (1 : ℝ) else 0) =
      (finiteBelowCount s S : ℝ) / n := by
    simp [finiteMean, finiteBelowCount]
  rw [hBelow] at hSum
  linarith

theorem interlaced_above_fraction_bound {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ) (S : ℝ)
    (hAB : ∀ i j : Fin n, j.val = i.val + 1 → a j ≤ b i) :
    finiteMean (fun i => if S ≤ a i then (1 : ℝ) else 0) ≤
      finiteMean (fun i => if S ≤ b i then (1 : ℝ) else 0) + 1 / n := by
  have hCount : (finiteBelowCount b S : ℝ) ≤ (finiteBelowCount a S : ℝ) + 1 := by
    exact_mod_cast finite_below_count_le_of_one_shift a b S hAB
  have hFrac := div_le_div_of_nonneg_right hCount (show (0 : ℝ) ≤ n by positivity)
  rw [add_div] at hFrac
  rw [finite_above_fraction_eq_below_complement hn, finite_above_fraction_eq_below_complement hn]
  linarith

theorem bounded_test_clipping_error {n : ℕ} (s : Fin n → ℝ≥0) (f : ℝ≥0 → ℝ)
    (M : ℝ) (hM : ∀ t, |f t| ≤ M) (S : ℝ≥0) :
    |finiteMean (fun i => f (s i)) - finiteMean (fun i => f (min (s i) S))| ≤
      (2 * |M|) * finiteMean (fun i => if (S : ℝ) ≤ s i then (1 : ℝ) else 0) := by
  have hPoint (i : Fin n) : |f (s i) - f (min (s i) S)| ≤
      (2 * |M|) * (if (S : ℝ) ≤ s i then (1 : ℝ) else 0) := by
    by_cases h : (S : ℝ) ≤ s i
    · rw [if_pos h, mul_one]
      have h1 := (hM (s i)).trans (le_abs_self M)
      have h2 := (hM (min (s i) S)).trans (le_abs_self M)
      have hT := abs_sub_le (f (s i)) 0 (f (min (s i) S))
      simp only [sub_zero, zero_sub, abs_neg] at hT
      linarith
    · have hSmall : s i ≤ S := by exact_mod_cast (le_of_not_ge h : (s i : ℝ) ≤ S)
      rw [if_neg h, min_eq_left hSmall]
      simp
  rw [← finiteMean_sub]
  exact (abs_finiteMean_le _).trans ((finiteMean_mono hPoint).trans_eq (finiteMean_const_mul _ _))

theorem continuous_clipped_mean_error_coefficient (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (M : ℝ) (hM : ∀ t, |f t| ≤ M) (S : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n → ∀ a b : Fin n → ℝ≥0,
      |finiteMean (fun i => f (min (a i) S)) - finiteMean (fun i => f (min (b i) S))| ≤
        ε + C * finiteMean (fun i => |min (a i : ℝ) (S : ℝ) - min (b i : ℝ) (S : ℝ)|) := by
  have hUniform := isCompact_Icc.uniformContinuousOn_of_continuous
    (hf.continuousOn : ContinuousOn f (Set.Icc 0 S))
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.mp hUniform ε hε
  let C := (2 * |M|) / δ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n hn a b
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hPoint (i : Fin n) : |f (min (a i) S) - f (min (b i) S)| ≤
      ε + C * |min (a i : ℝ) (S : ℝ) - min (b i : ℝ) (S : ℝ)| := by
    by_cases hD : |min (a i : ℝ) (S : ℝ) - min (b i : ℝ) (S : ℝ)| < δ
    · have hDist : dist (min (a i) S) (min (b i) S) < δ := by
        change dist (min (a i : ℝ) (S : ℝ)) (min (b i : ℝ) (S : ℝ)) < δ
        rwa [Real.dist_eq]
      have h := hU (min (a i) S) ⟨by positivity, min_le_right _ _⟩
        (min (b i) S) ⟨by positivity, min_le_right _ _⟩ hDist
      rw [Real.dist_eq] at h
      exact h.le.trans (le_add_of_nonneg_right (mul_nonneg hC (abs_nonneg _)))
    · have hDLe := le_of_not_gt hD
      have hMul := mul_le_mul_of_nonneg_left hDLe hC
      have hCancel : C * δ = 2 * |M| := div_mul_cancel₀ _ hδ.ne'
      rw [hCancel] at hMul
      have h1 := (hM (min (a i) S)).trans (le_abs_self M)
      have h2 := (hM (min (b i) S)).trans (le_abs_self M)
      have hT := abs_sub_le (f (min (a i) S)) 0 (f (min (b i) S))
      simp only [sub_zero, zero_sub, abs_neg] at hT
      linarith
  rw [← finiteMean_sub]
  apply (abs_finiteMean_le _).trans
  calc
    _ ≤ finiteMean (fun i => ε + C *
        |min (a i : ℝ) (S : ℝ) - min (b i : ℝ) (S : ℝ)|) := finiteMean_mono hPoint
    _ = _ := by rw [finiteMean_add, finiteMean_const, finiteMean_const_mul]

theorem interlaced_bounded_continuous_mean_error_coefficient (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (M : ℝ) (hM : ∀ t, |f t| ≤ M) (S : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n → ∀ a b : Fin n → ℝ≥0,
      Antitone (fun i => (a i : ℝ)) → Antitone (fun i => (b i : ℝ)) →
      (∀ i j : Fin n, j.val = i.val + 1 → (a j : ℝ) ≤ b i) →
      (∀ i j : Fin n, j.val = i.val + 1 → (b j : ℝ) ≤ a i) →
      |finiteMean (fun i => f (a i)) - finiteMean (fun i => f (b i))| ≤
        ε + C / n + (4 * |M|) *
          finiteMean (fun i => if (S : ℝ) ≤ b i then (1 : ℝ) else 0) := by
  obtain ⟨D, hD, hClip⟩ := continuous_clipped_mean_error_coefficient f hf M hM S hε
  refine ⟨D * (2 * S) + 2 * |M|, by positivity, ?_⟩
  intro n hn a b ha hb hAB hBA
  have hDistance := clipped_interlaced_array_mean_distance_bound
    (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) ha hb
    (fun i => (a i).coe_nonneg) (fun i => (b i).coe_nonneg) hAB hBA S S.coe_nonneg
  have hDC := mul_le_mul_of_nonneg_left hDistance hD
  have hClipBound := hClip hn a b
  have hTailA := bounded_test_clipping_error a f M hM S
  have hTailB := bounded_test_clipping_error b f M hM S
  have hTailCount := interlaced_above_fraction_bound hn
    (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) S hAB
  have hTailProduct := mul_le_mul_of_nonneg_left hTailCount (by positivity : 0 ≤ 2 * |M|)
  have hT1 := abs_sub_le (finiteMean (fun i => f (a i))) (finiteMean (fun i => f (min (a i) S)))
    (finiteMean (fun i => f (b i)))
  have hT2 := abs_sub_le (finiteMean (fun i => f (min (a i) S)))
    (finiteMean (fun i => f (min (b i) S))) (finiteMean (fun i => f (b i)))
  rw [abs_sub_comm (finiteMean (fun i => f (min (b i) S)))] at hT2
  have hAlg : (D * (2 * (S : ℝ)) + 2 * |M|) / (n : ℝ) =
      D * (2 * (S : ℝ) / n) + 2 * |M| * (1 / n) := by ring
  rw [hAlg]
  nlinarith

end CircularLaw
