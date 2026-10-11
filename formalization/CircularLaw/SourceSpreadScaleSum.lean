import CircularLaw.SourceSpreadProbability

/-!
# The complete spread-family scale sum

Both source mass cases and every exponent `4 <= u <= vL` are summed.
Each vector contributes its supremum over all deterministic shifts.
The scale count and displayed scalar-grid prefactor are absorbed into
a positive multiple of `n*log(d)` in the failure exponent.
-/

noncomputable section
open Classical Filter
open scoped BigOperators Topology

namespace CircularLaw

def sourceSpreadProbabilitySum (n d L : ℕ) (a₃ R : ℝ)
    (hFinite : ∀ u ∈ Finset.Icc 4 (structuralTerminalExponent n d L),
      (canonicalApproxFamily (d ^ u) (sourceSpreadFamily n d L a₃ (1 / 4608) u)).Finite)
    (I : Finset (Fin n)) : ℝ :=
  ∑ u : {u : ℕ // u ∈ Finset.Icc 4 (structuralTerminalExponent n d L)},
    @canonicalFamilySupProbabilitySum n
      (canonicalApproxFamily (d ^ u.val) (sourceSpreadFamily n d L a₃ (1 / 4608) u.val))
      (hFinite u.val u.property).fintype I (d ^ u.val) d R

theorem sourceSpread_scale_prefactor_absorbed {n d v : ℕ} {r : ℝ}
    (hd : 0 < d) (hLog : 1 ≤ Real.log d) (hv : (v : ℝ) ≤ 2 * d)
    (hN : Real.log 16 + 3 ≤ (r / 4) * n) :
    2 * (d : ℝ) ^ 2 * ((v : ℝ) * (4 * Real.exp (-(r / 2) * n * Real.log d))) ≤
      Real.exp (-(r / 4) * n * Real.log d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hPrefactor : 2 * (d : ℝ) ^ 2 * v * 4 ≤ 16 * (d : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg (d : ℝ))]
  have hLog16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have hExponent : Real.log 16 + 3 * Real.log d ≤ (r / 4) * n * Real.log d := by
    have hConst := mul_le_mul_of_nonneg_left hLog hLog16
    have hDimension := mul_le_mul_of_nonneg_right hN (show 0 ≤ Real.log d by linarith)
    nlinarith only [hConst, hDimension]
  have hExpD : Real.exp (3 * Real.log d) = (d : ℝ) ^ 3 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hdR] using Real.exp_nat_mul (Real.log d) 3
  calc
    _ = (2 * (d : ℝ) ^ 2 * v * 4) * Real.exp (-(r / 2) * n * Real.log d) := by ring
    _ ≤ (16 * (d : ℝ) ^ 3) * Real.exp (-(r / 2) * n * Real.log d) :=
      mul_le_mul_of_nonneg_right hPrefactor (Real.exp_nonneg _)
    _ = Real.exp (Real.log 16 + 3 * Real.log d) * Real.exp (-(r / 2) * n * Real.log d) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 16), hExpD]
    _ ≤ Real.exp ((r / 4) * n * Real.log d) * Real.exp (-(r / 2) * n * Real.log d) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hExponent) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem eventually_sourceSpread_scale_probability_uniform {a₃ C σ : ℝ}
    (ha : 0 < a₃) (hSmall : a₃ ≤ 1 / 65536) (hC : 96 ≤ C) (hσ : σ ≤ 1)
    (R : ℝ) (hR : 1 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, InLowerBand C σ n d →
      ∀ L : ℕ, IsKernelCodimension n d L →
      ∃ hFinite : ∀ u ∈ Finset.Icc 4 (structuralTerminalExponent n d L),
        (canonicalApproxFamily (d ^ u) (sourceSpreadFamily n d L a₃ (1 / 4608) u)).Finite,
      ∀ I : Finset (Fin n), I.card = n - L →
        sourceSpreadProbabilitySum n d L a₃ R hFinite I ≤
          Real.exp (-(sourceK1DecayExponent a₃ / 4) * n * Real.log d) ∧
        2 * (d : ℝ) ^ 2 * sourceSpreadProbabilitySum n d L a₃ R hFinite I ≤
          Real.exp (-(sourceK1DecayExponent a₃ / 4) * n * Real.log d) := by
  have hCPos : 0 < C := by linarith
  have hRate := sourceK1DecayExponent_pos ha
  have hDimension : ∀ᶠ n : ℕ in atTop,
      Real.log 16 + 3 ≤ (sourceK1DecayExponent a₃ / 4) * n := by
    have hCast := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    filter_upwards [hCast.eventually_ge_atTop ((Real.log 16 + 3) / (sourceK1DecayExponent a₃ / 4))]
      with n hn
    simpa only [mul_comm] using
      (div_le_iff₀ (by positivity : 0 < sourceK1DecayExponent a₃ / 4)).mp hn
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop)).eventually_ge_atTop 1
  filter_upwards [eventually_sourceSpread_probability_decay_uniform ha hSmall hC hσ R hR,
    eventually_source_kernel_conditions_uniform hCPos (1 + σ),
    eventually_degree_property_uniform hCPos hLog, hDimension]
    with n hSpread hConditions hLogDegree hDimension
  intro d hBand L hL
  have hCon := hConditions d hBand.1 hBand.2
  have hFiniteCon := source_kernel_dimension_twice_degree hCon
  have hd : 1 < d := by have h := hCon.degree_large; omega
  have hCubic : 4 * d ^ 3 ≤ n :=
    (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right hFiniteCon.2.1
      (by decide : 3 ≤ 4))).trans hCon.dimension_fourth
  have hAt (u : {u : ℕ // u ∈ Finset.Icc 4 (structuralTerminalExponent n d L)}) :=
    hSpread d hBand L hL u.val (Finset.mem_Icc.mp u.property).2
  choose hA hBound using hAt
  let hFinite : ∀ u ∈ Finset.Icc 4 (structuralTerminalExponent n d L),
      (canonicalApproxFamily (d ^ u) (sourceSpreadFamily n d L a₃ (1 / 4608) u)).Finite :=
    fun u hu => hA ⟨u, hu⟩
  refine ⟨hFinite, ?_⟩
  intro I hI
  have hIndex : (Finset.Icc 4 (structuralTerminalExponent n d L)).card ≤
      structuralTerminalExponent n d L := by rw [Nat.card_Icc]; omega
  have hSum : sourceSpreadProbabilitySum n d L a₃ R hFinite I ≤
      (structuralTerminalExponent n d L : ℝ) *
        (4 * Real.exp (-(sourceK1DecayExponent a₃ / 2) * n * Real.log d)) := by
    unfold sourceSpreadProbabilitySum
    apply (Finset.sum_le_sum (fun u _ => hBound u I hI)).trans
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hIndex) (by positivity)
  have hScaled := mul_le_mul_of_nonneg_left hSum (by positivity : 0 ≤ 2 * (d : ℝ) ^ 2)
  have hAll := hScaled.trans (sourceSpread_scale_prefactor_absorbed hFiniteCon.2.1
    (hLogDegree d hBand.1)
    (structuralTerminalExponent_linear_bound hd hCubic hL (hLogDegree d hBand.1)) hDimension)
  refine ⟨?_, hAll⟩
  apply le_trans ?_ hAll
  have hPrefactor : (1 : ℝ) ≤ 2 * (d : ℝ) ^ 2 := by
    have hD : (1 : ℝ) ≤ d := by exact_mod_cast hFiniteCon.2.1
    nlinarith
  apply le_mul_of_one_le_left ?_ hPrefactor
  unfold sourceSpreadProbabilitySum
  apply Finset.sum_nonneg
  intro u _
  exact @canonicalFamilySupProbabilitySum_nonneg n
    (canonicalApproxFamily (d ^ u.val) (sourceSpreadFamily n d L a₃ (1 / 4608) u.val))
    (hFinite u.val u.property).fintype I (d ^ u.val) d R

end CircularLaw
