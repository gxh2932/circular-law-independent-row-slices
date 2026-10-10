import CircularLaw.SourceGraphGap
import CircularLaw.SourceGraphGrowthRange

/-!
# Iterated spreading of actual near-kernel vectors

The actual integer growth sequence propagates a starting coordinate
lower bound to its first exit rank. The image-energy threshold and final
coordinate radius are explicit. Only the uniform source graph events
are assumed; growth, ceiling, rank validity and iteration are proved.
-/

noncomputable section
open Classical
open scoped BigOperators NNReal InnerProductSpace

namespace CircularLaw

def sourceGraphIterationSteps (C n : ℝ) (k : ℕ) : ℕ :=
  Nat.ceil (4 * C * Real.log (n / k) ^ 4) + 1

def sourceGraphIterationRadius (C β n d : ℝ) (k : ℕ) (a : ℝ) : ℝ :=
  a * ((β * k / (d * n)) ^ 7) ^ sourceGraphIterationSteps C n k

set_option maxHeartbeats 1000000 in
theorem source_terminal_graph_gap_image_spread {ρ : Type*} [Fintype ρ]
    {m ell : ℕ} (A : Matrix ρ (Fin m) ℂ) (e : ρ ↪ Fin m) (z : ℂ)
    (v : EuclideanSpace ℂ (Fin m)) {K β n d k : ℝ}
    (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1) (hn : 0 < n)
    (hd : Real.exp (Real.exp 1) ≤ d) (hAmbient : n / 2 ≤ (m : ℝ))
    (hEll : 0 < ell) (hLo : k ≤ ell) (hHi : (ell : ℝ) ≤ sourceGraphTerminalScale n d)
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K n d)
    (hUnique : MatrixUniqueExpansionBudget A e β n d k (sourceGraphTerminalScale n d))
    (hHeavy : MatrixHeavyRowBudget A β n d)
    (hGap : orderedNormAt (fun j => v j)
      (ell + sourceGraphGrowth (graphGrowthConstant (K + 1)) n d ell) ≤
      orderedNormAt (fun j => v j) ell * (β * ell / (d * n)) ^ 7) :
    sourceGraphExpansion n d ell / 2 ≤
      ((coordinateSpreadSet ((diagonalEmbeddedShift A e z).toEuclideanLin v)
        (β * orderedNormAt (fun j => v j) ell / 2)).card : ℝ) := by
  have hE : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hExp : 4 ≤ Real.exp (1 + 1) := by rw [Real.exp_add]; nlinarith
  have hdFour : 4 ≤ d := hExp.trans
    ((Real.exp_le_exp.mpr (by linarith : (1 : ℝ) + 1 ≤ Real.exp 1)).trans hd)
  obtain ⟨hu, hUpper, hLogU⟩ := source_graph_terminal_range hn hd
  have hEllReal : 0 < (ell : ℝ) := by exact_mod_cast hEll
  have hEllN : (ell : ℝ) ≤ n := by linarith
  have hLogEll : 1 ≤ Real.log (n / ell) := hLogU.trans
    (Real.log_le_log (div_pos hn hu) (div_le_div_of_nonneg_left hn.le hEllReal hHi))
  have hC : 1 ≤ graphGrowthConstant (K + 1) := graph_growth_constant_ge_one (by linarith)
  have hRank := source_graph_growth_next_rank_valid hC (by linarith : 1 ≤ d)
    hEll hHi hLogEll (by linarith : 2 * sourceGraphTerminalScale n d ≤ (m : ℝ))
  exact source_graph_ordered_gap_image_spread A e z v hK hβ hβOne hn hdFour hEll hEllN
    hLogEll hLo hHi hRank hz hzUpper hColumns hUnique hHeavy hGap

theorem source_graph_expansion_mono {n d k x : ℝ}
    (hn : 0 < n) (hd : 0 ≤ d) (hk : 0 < k) (hkx : k ≤ x)
    (hLog : 1 ≤ Real.log (n / x)) :
    sourceGraphExpansion n d k ≤ sourceGraphExpansion n d x := by
  have hx : 0 < x := hk.trans_le hkx
  have hLp : 0 < Real.log (n / x) := by linarith
  have hLLe : Real.log (n / x) ≤ Real.log (n / k) :=
    Real.log_le_log (div_pos hn hx) (div_le_div_of_nonneg_left hn.le hk hkx)
  have hLkp : 0 < Real.log (n / k) := hLp.trans_le hLLe
  have hSquare := (sq_le_sq₀ hLp.le hLkp.le).mpr hLLe
  unfold sourceGraphExpansion
  apply (div_le_div_iff₀ (pow_pos hLkp 2) (pow_pos hLp 2)).mpr
  calc
    d * k * Real.log (n / x) ^ 2 ≤ d * x * Real.log (n / x) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkx hd) (sq_nonneg _)
    _ ≤ d * x * Real.log (n / k) ^ 2 :=
      mul_le_mul_of_nonneg_left hSquare (mul_nonneg hd hx.le)

theorem source_graph_gap_ratio_mono {β n d k x : ℝ}
    (hβ : 0 ≤ β) (hn : 0 < n) (hd : 0 < d) (hk : 0 ≤ k) (hkx : k ≤ x) :
    (β * k / (d * n)) ^ 7 ≤ (β * x / (d * n)) ^ 7 := by
  have hRatio := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkx hβ)
    (mul_pos hd hn).le
  exact pow_le_pow_left₀ (by positivity : 0 ≤ β * k / (d * n)) hRatio 7

theorem source_graph_gap_ratio_range {β n d k : ℝ}
    (hβ : 0 < β) (hβOne : β ≤ 1) (hn : 0 < n) (hd : 1 ≤ d)
    (hk : 0 < k) (hkn : k ≤ n) :
    0 < (β * k / (d * n)) ^ 7 ∧ (β * k / (d * n)) ^ 7 ≤ 1 := by
  have hdp : 0 < d := by linarith
  have hRatioPos : 0 < β * k / (d * n) := by positivity
  have hRatioOne : β * k / (d * n) ≤ 1 := by
    apply (div_le_one (mul_pos hdp hn)).mpr
    calc
      β * k ≤ k := mul_le_of_le_one_left hk.le hβOne
      _ ≤ n := hkn
      _ ≤ d * n := le_mul_of_one_le_left hn.le hd
  exact ⟨pow_pos hRatioPos 7, pow_le_one₀ hRatioPos.le hRatioOne⟩

theorem ordered_prefix_card_le_coordinate_spread {m s : ℕ}
    (v : EuclideanSpace ℂ (Fin m)) (hs : 0 < s) (hsm : s ≤ m) {a : ℝ}
    (hLower : a ≤ orderedNormAt (fun j => v j) s) :
    s ≤ (coordinateSpreadSet v a).card := by
  have hSubset : orderedPrefix (fun j => v j) s ⊆ coordinateSpreadSet v a := by
    intro j hj
    exact (coordinate_spread_set_mem v a j).mpr
      (hLower.trans (orderedNormAt_le_norm_mem_prefix _ hs hsm j hj))
  exact (orderedPrefix_card _ hsm).symm ▸ Finset.card_le_card hSubset

set_option maxHeartbeats 1500000 in
theorem source_graph_near_kernel_iterated_spread {ρ : Type*} [Fintype ρ]
    {m k : ℕ} (A : Matrix ρ (Fin m) ℂ) (e : ρ ↪ Fin m) (z : ℂ)
    (v : EuclideanSpace ℂ (Fin m)) {K β n d u a : ℝ}
    (hK : 0 ≤ K) (hβ : 0 < β) (hβOne : β ≤ 1) (hn : 0 < n) (hd : 4 ≤ d)
    (hk : 0 < k) (hku : (k : ℝ) ≤ u) (hu : 0 < u) (huN : u ≤ n)
    (hLog : 1 ≤ Real.log (n / u)) (hAmbient : 2 * u ≤ (m : ℝ))
    (hz : β ≤ ‖z‖) (hzUpper : ‖z‖ ≤ d)
    (hColumns : MatrixColumnDegreeBudget A K n d)
    (hUnique : MatrixUniqueExpansionBudget A e β n d k u)
    (hHeavy : MatrixHeavyRowBudget A β n d)
    (ha : 0 < a) (hInitial : a ≤ orderedNormAt (fun j => v j) k)
    (hSmall : ‖(diagonalEmbeddedShift A e z).toEuclideanLin v‖ ^ 2 <
      sourceGraphExpansion n d k * β ^ 2 *
        sourceGraphIterationRadius (graphGrowthConstant (K + 1)) β n d k a ^ 2 / 8) :
    u < ((coordinateSpreadSet v
      (sourceGraphIterationRadius (graphGrowthConstant (K + 1)) β n d k a)).card : ℝ) := by
  classical
  let C := graphGrowthConstant (K + 1)
  let r := sourceGraphRankSequence C n d k
  let δ := (β * k / (d * n)) ^ 7
  let T := sourceGraphIterationSteps C n k
  let R := sourceGraphIterationRadius C β n d k a
  have hC : 1 ≤ C := graph_growth_constant_ge_one (by linarith : 0 ≤ K + 1)
  have hCp : 0 < C := by linarith
  have hdp : 0 < d := by linarith
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkn : (k : ℝ) ≤ n := hku.trans huN
  obtain ⟨hδPos, hδOne⟩ := source_graph_gap_ratio_range hβ hβOne hn
    (by linarith : 1 ≤ d) hkReal hkn
  have hRPos : 0 < R := by dsimp [R, sourceGraphIterationRadius]; positivity
  obtain ⟨j, hj, hExit⟩ := source_graph_rank_sequence_exits_by hC hn (by linarith : 1 ≤ d)
    hk hu hku hLog
  let hExists : ∃ i, u < (r i : ℝ) := ⟨j, hExit⟩
  let τ := Nat.find hExists
  have hτExit : u < (r τ : ℝ) := Nat.find_spec hExists
  have hτT : τ ≤ T := (Nat.find_min' hExists hExit).trans hj
  have hBefore : ∀ i < τ, (r i : ℝ) ≤ u := fun i hi =>
    le_of_not_gt (Nat.find_min hExists hi)
  have hLogR : ∀ i < τ, 1 ≤ Real.log (n / r i) := by
    intro i hi
    have hrPos : 0 < (r i : ℝ) := by exact_mod_cast source_graph_rank_sequence_pos C n d hk i
    exact hLog.trans (Real.log_le_log (div_pos hn hu)
      (div_le_div_of_nonneg_left hn.le hrPos (hBefore i hi)))
  have hRanks : ∀ i ≤ τ, r i ≤ m := by
    intro i hi
    cases i with
    | zero =>
      have hkm : (k : ℝ) ≤ m := by linarith
      exact_mod_cast hkm
    | succ i =>
      have hiτ : i < τ := by omega
      dsimp only [r]
      rw [source_graph_rank_sequence_succ]
      exact source_graph_growth_next_rank_valid hC (by linarith : 1 ≤ d)
        (source_graph_rank_sequence_pos C n d hk i) (hBefore i hiτ) (hLogR i hiτ) hAmbient
  have hChain : ∀ i ≤ τ, a * δ ^ i ≤ orderedNormAt (fun j => v j) (r i) := by
    intro i hi
    induction i with
    | zero => simpa only [pow_zero, mul_one, r, source_graph_rank_sequence_zero] using hInitial
    | succ i ih =>
      have hiτ : i < τ := by omega
      have hPrev := ih hiτ.le
      have hiT : i ≤ T := hiτ.le.trans hτT
      have hPower : δ ^ T ≤ δ ^ i := pow_le_pow_of_le_one hδPos.le hδOne hiT
      have hRadius : R ≤ orderedNormAt (fun j => v j) (r i) :=
        (mul_le_mul_of_nonneg_left hPower ha.le).trans hPrev
      have hkr : (k : ℝ) ≤ r i := by exact_mod_cast source_graph_rank_sequence_ge_initial C n d k i
      have hrPos : 0 < (r i : ℝ) := hkReal.trans_le hkr
      have hExp := source_graph_expansion_mono hn hdp.le hkReal hkr (hLogR i hiτ)
      have hExpPos : 0 ≤ sourceGraphExpansion n d (r i) := by
        unfold sourceGraphExpansion
        positivity
      have hCoeff := mul_le_mul_of_nonneg_right hExp (sq_nonneg β)
      have hSquared := (sq_le_sq₀ hRPos.le (orderedNormAt_nonneg (fun j => v j) (r i))).mpr hRadius
      have hProduct := mul_le_mul hCoeff hSquared (sq_nonneg R) (mul_nonneg hExpPos (sq_nonneg β))
      have hSmallAt : ‖(diagonalEmbeddedShift A e z).toEuclideanLin v‖ ^ 2 <
          sourceGraphExpansion n d (r i) * β ^ 2 * orderedNormAt (fun j => v j) (r i) ^ 2 / 8 :=
        hSmall.trans_le (div_le_div_of_nonneg_right hProduct (by norm_num : (0 : ℝ) ≤ 8))
      have hNextRank : r i + sourceGraphGrowth C n d (r i) ≤ m := by
        have h := hRanks (i + 1) hi
        simpa only [r, source_graph_rank_sequence_succ] using h
      have hStep := source_graph_ordered_coordinate_no_gap A e z v hK hβ hβOne hn hd
        (source_graph_rank_sequence_pos C n d hk i) ((hBefore i hiτ).trans huN)
        (hLogR i hiτ) hkr (hBefore i hiτ) hNextRank hz hzUpper hColumns hUnique hHeavy hSmallAt
      have hδLe := source_graph_gap_ratio_mono hβ.le hn hdp hkReal.le hkr
      have hFirst := mul_le_mul_of_nonneg_right hPrev hδPos.le
      have hSecond := mul_le_mul_of_nonneg_left hδLe (orderedNormAt_nonneg (fun j => v j) (r i))
      have hLower : a * δ ^ (i + 1) ≤ orderedNormAt (fun j => v j)
          (r i + sourceGraphGrowth C n d (r i)) := by
        calc
          _ = (a * δ ^ i) * δ := by rw [pow_succ]; ring
          _ ≤ orderedNormAt (fun j => v j) (r i) * δ := hFirst
          _ ≤ orderedNormAt (fun j => v j) (r i) * (β * r i / (d * n)) ^ 7 := hSecond
          _ ≤ orderedNormAt (fun j => v j) (r i + sourceGraphGrowth C n d (r i)) := hStep.le
      simpa only [r, source_graph_rank_sequence_succ] using hLower
  have hFinal : R ≤ orderedNormAt (fun j => v j) (r τ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hδPos.le hδOne hτT) ha.le).trans
      (hChain τ le_rfl)
  have hCount := ordered_prefix_card_le_coordinate_spread v
    (source_graph_rank_sequence_pos C n d hk τ) (hRanks τ le_rfl) hFinal
  have hCountReal : (r τ : ℝ) ≤ ((coordinateSpreadSet v R).card : ℝ) := by exact_mod_cast hCount
  exact hτExit.trans_le hCountReal

end CircularLaw
