import CircularLaw.RowLoadRates

/-!
# Uniform row loads at both LLY ranks

The second and third blocks use their own rank-dependent cutoffs. The
union ranges over every coordinate subset before any vector is chosen.
-/

noncomputable section
open Classical Filter

namespace CircularLaw

def LLYRowLoad {n d : ℕ} (I : Finset (Fin n)) (k₂ k₃ : ℕ)
    (rows : RowSliceMatrix n d) : Prop := SourceRowLoad I k₂ rows ∧ SourceRowLoad I k₃ rows

theorem uniform_row_load_failure_entropy_of_rank_bound {n d k : ℕ}
    (hd : 0 < d) (hdn : d ≤ n) (hk : 0 < k) {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1)
    (hRank : (k : ℝ) ≤ a * n) (I : Finset (Fin n)) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬SourceRowLoad I k rows) ≤
      Real.exp ((n : ℝ) * smallSetEntropy (1 / (16 * (d : ℝ))) - rowLoadRate * I.card) +
      Real.exp ((n : ℝ) * smallSetEntropy a - rowLoadRate * I.card) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht : (0 : ℝ) < 1 / (16 * (d : ℝ)) := by positivity
  have htOne : 1 / (16 * (d : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * d)).mpr
    linarith
  have hSize0 : (almostConstantRank n d : ℝ) ≤ (1 / (16 * (d : ℝ))) * n := by
    convert almostConstantRank_upper (n := n) hd using 1
    ring
  have hEntropy0 := smallCoordinateSets_card_density ht htOne hSize0
  have hEntropy := smallCoordinateSets_card_density ha haOne hRank
  apply (uniform_row_load_failure_counting hd hdn hk I).trans
  calc
    _ ≤ (Real.exp ((n : ℝ) * smallSetEntropy (1 / (16 * (d : ℝ)))) +
        Real.exp ((n : ℝ) * smallSetEntropy a)) * Real.exp (-rowLoadRate * I.card) :=
      mul_le_mul_of_nonneg_right (add_le_add hEntropy0 hEntropy) (Real.exp_pos _).le
    _ = _ := by simp only [add_mul, ← Real.exp_add, sub_eq_add_neg, neg_mul]

theorem lly_row_load_failure_entropy {n d k₂ k₃ : ℕ}
    (hd : 0 < d) (hdn : d ≤ n) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1)
    (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n) (I : Finset (Fin n)) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬LLYRowLoad I k₂ k₃ rows) ≤
      2 * (Real.exp ((n : ℝ) * smallSetEntropy (1 / (16 * (d : ℝ))) - rowLoadRate * I.card) +
        Real.exp ((n : ℝ) * smallSetEntropy a - rowLoadRate * I.card)) := by
  apply (uniformProbability_mono (fun _ h => _root_.not_and_or.mp h)).trans
    ((uniformProbability_or_le _ _).trans ?_)
  have h := add_le_add (uniform_row_load_failure_entropy_of_rank_bound hd hdn hk₂ ha haOne hRank₂ I)
    (uniform_row_load_failure_entropy_of_rank_bound hd hdn hk₃ ha haOne hRank₃ I)
  simpa only [two_mul] using h

theorem lly_row_load_failure_absorbed {n d k₂ k₃ : ℕ}
    (hd : 0 < d) (hdn : d ≤ n) (hk₂ : 0 < k₂) (hk₃ : 0 < k₃)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1)
    (hRank₂ : (k₂ : ℝ) ≤ a * n) (hRank₃ : (k₃ : ℝ) ≤ a * n) (I : Finset (Fin n))
    (hRows : (99 / 100 : ℝ) * n ≤ I.card)
    (hEntropy0 : smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4)
    (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4)
    (hDimension : 4 * Real.log 4 ≤ rowLoadRate * n) :
    uniformProbability (fun rows : RowSliceMatrix n d => ¬LLYRowLoad I k₂ k₃ rows) ≤
      Real.exp (-(rowLoadRate / 4) * n) := by
  have hRowScaled := mul_le_mul_of_nonneg_left hRows rowLoadRate_pos.le
  have hSmall0 := mul_le_mul_of_nonneg_left hEntropy0 (Nat.cast_nonneg (α := ℝ) n)
  have hSmall := mul_le_mul_of_nonneg_left hEntropy (Nat.cast_nonneg (α := ℝ) n)
  have hNRate : (0 : ℝ) ≤ rowLoadRate * n := mul_nonneg rowLoadRate_pos.le (Nat.cast_nonneg n)
  have hExp0 : Real.exp ((n : ℝ) * smallSetEntropy (1 / (16 * (d : ℝ))) - rowLoadRate * I.card) ≤
      Real.exp (-(rowLoadRate / 2) * n) := Real.exp_le_exp.mpr (by nlinarith)
  have hExp : Real.exp ((n : ℝ) * smallSetEntropy a - rowLoadRate * I.card) ≤
      Real.exp (-(rowLoadRate / 2) * n) := Real.exp_le_exp.mpr (by nlinarith)
  apply (lly_row_load_failure_entropy hd hdn hk₂ hk₃ ha haOne hRank₂ hRank₃ I).trans
  calc
    _ ≤ 2 * (Real.exp (-(rowLoadRate / 2) * n) + Real.exp (-(rowLoadRate / 2) * n)) := by
      gcongr
    _ = 4 * Real.exp (-(rowLoadRate / 2) * n) := by ring
    _ = Real.exp (Real.log 4) * Real.exp (-(rowLoadRate / 2) * n) := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    _ = Real.exp (Real.log 4 - (rowLoadRate / 2) * n) := by
      rw [← Real.exp_add, sub_eq_add_neg, neg_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventually_lly_row_load_failure_uniform {C a : ℝ} (hC : 0 < C)
    (ha : 0 < a) (haOne : a ≤ 1) (hEntropy : smallSetEntropy a ≤ rowLoadRate / 4) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, C * Real.log n ≤ (d : ℝ) → d ≤ n →
      ∀ k₂ k₃ : ℕ, 0 < k₂ → 0 < k₃ → (k₂ : ℝ) ≤ a * n → (k₃ : ℝ) ≤ a * n →
        ∀ I : Finset (Fin n), (99 / 100 : ℝ) * n ≤ I.card →
          uniformProbability (fun rows : RowSliceMatrix n d => ¬LLYRowLoad I k₂ k₃ rows) ≤
            Real.exp (-(rowLoadRate / 4) * n) := by
  have hDegree : ∀ᶠ d : ℕ in atTop, 0 < d ∧
      smallSetEntropy (1 / (16 * (d : ℝ))) ≤ rowLoadRate / 4 := by
    filter_upwards [eventually_gt_atTop 0, eventually_row_load_degree_entropy] with d hd hEntropy0
    exact ⟨hd, hEntropy0⟩
  have hDimension : ∀ᶠ n : ℕ in atTop, 4 * Real.log 4 / rowLoadRate ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop _
  filter_upwards [eventually_degree_property_uniform hC hDegree, hDimension] with n hDegree hDimension
  intro d hLower hdn k₂ k₃ hk₂ hk₃ hRank₂ hRank₃ I hRows
  obtain ⟨hd, hEntropy0⟩ := hDegree d hLower
  apply lly_row_load_failure_absorbed hd hdn hk₂ hk₃ ha haOne hRank₂ hRank₃ I hRows hEntropy0 hEntropy
  have h := (div_le_iff₀ rowLoadRate_pos).mp hDimension
  nlinarith only [h]

end CircularLaw
