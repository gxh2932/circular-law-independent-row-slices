import CircularLaw.RowReplacementProbability
import CircularLaw.BernoulliPrincipalMinorLaw

/-!
# Prefix row pairs from the actual independent square matrices

The square coupling is the product of the literal row-slice matrix law
and sparse Bernoulli entry law. Its injectively selected paired rows have
exactly the finite product law used in the row replacement proof.
-/

noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace CircularLaw

def independentSquareComparisonLaw (n d : ℕ) :
    Measure (RowSliceMatrix n d × BernoulliSquareSample n) :=
  (rowSliceMatrixLaw n d).prod (sparseBernoulliMatrixLaw n d)

instance independentSquareComparisonLaw_finite (n d : ℕ) :
    IsFiniteMeasure (independentSquareComparisonLaw n d) := by
  unfold independentSquareComparisonLaw rowSliceMatrixLaw
  infer_instance

theorem independentSquareComparisonLaw_probability {n d : ℕ} (hdn : d ≤ n) :
    IsProbabilityMeasure (independentSquareComparisonLaw n d) := by
  haveI := rowSliceMatrixLaw_probability hdn
  unfold independentSquareComparisonLaw
  infer_instance

theorem bernoulli_row_flatten_law (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    (Measure.pi (fun _ : Fin n => bernoulliCubeLaw (Fin n) p hp)).map
      (fun rows : Fin n → Fin n → Bool => fun ij : Fin n × Fin n => rows ij.1 ij.2) =
      bernoulliSquareMatrixLaw n p hp := by
  apply Measure.ext_of_singleton
  intro y
  have hPre : (fun rows : Fin n → Fin n → Bool => fun ij : Fin n × Fin n => rows ij.1 ij.2) ⁻¹' {y} =
      {fun i j => y (i, j)} := by
    ext rows
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      funext i j
      exact congrFun h (i, j)
    · intro h
      funext ij
      exact congrFun (congrFun h ij.1) ij.2
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton y), hPre]
  simp only [bernoulliSquareMatrixLaw, bernoulliCubeLaw, Measure.pi_singleton]
  rw [Fintype.prod_prod_type]

def squareRowPairsToSamples {n d : ℕ} (rows : Fin n → ReplacementRowPair n d) :
    RowSliceMatrix n d × BernoulliSquareSample n :=
  ((fun i => (rows i).1), (fun ij => (rows ij.1).2 ij.2))

theorem square_row_pairs_to_samples_law {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    (Measure.pi (fun _ : Fin n => replacementRowPairLaw hn hdn)).map squareRowPairsToSamples =
      independentSquareComparisonLaw n d := by
  haveI := rowSliceLaw_probability hdn
  let p := rowBernoulliParameter n d
  let hp := rowBernoulliParameter_le_one hn hdn
  let e := MeasurableEquiv.arrowProdEquivProdArrow (RowSlice n d) (Fin n → Bool) (Fin n)
  let g := Prod.map (id : RowSliceMatrix n d → RowSliceMatrix n d)
    (fun rows : Fin n → Fin n → Bool => fun ij : Fin n × Fin n => rows ij.1 ij.2)
  have hPair := (measurePreserving_arrowProdEquivProdArrow (RowSlice n d) (Fin n → Bool) (Fin n)
    (fun _ => rowSliceLaw n d) (fun _ => bernoulliCubeLaw (Fin n) p hp)).map_eq
  have hMap : (Measure.pi (fun _ : Fin n => replacementRowPairLaw hn hdn)).map squareRowPairsToSamples =
      ((Measure.pi (fun _ : Fin n => replacementRowPairLaw hn hdn)).map e).map g := by
    rw [Measure.map_map (measurable_of_countable g) e.measurable]
    rfl
  rw [hMap]
  change ((Measure.pi (fun _ : Fin n => (rowSliceLaw n d).prod
    (bernoulliCubeLaw (Fin n) p hp))).map e).map g = _
  rw [hPair]
  rw [← Measure.map_prod_map _ _ measurable_id (measurable_of_countable _), Measure.map_id,
    bernoulli_row_flatten_law, ← rowSliceMatrixLaw_eq_pi hdn]
  exact congrArg (fun ν => (rowSliceMatrixLaw n d).prod ν) (sparseBernoulliMatrixLaw_eq hn hdn).symm

def squareComparisonPrefixPairs {k n d : ℕ} (f : Fin k ↪ Fin n)
    (samples : RowSliceMatrix n d × BernoulliSquareSample n) : Fin k → ReplacementRowPair n d :=
  fun i => (samples.1 (f i), fun j => samples.2 (f i, j))

theorem independent_square_prefix_pairs_law {k n d : ℕ} (hn : 0 < n) (hdn : d ≤ n)
    (f : Fin k ↪ Fin n) :
    (independentSquareComparisonLaw n d).map (squareComparisonPrefixPairs f) =
      Measure.pi (fun _ : Fin k => replacementRowPairLaw hn hdn) := by
  rw [← square_row_pairs_to_samples_law hn hdn,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  change (Measure.pi (fun _ : Fin n => replacementRowPairLaw hn hdn)).map
    (fun rows i => rows (f i)) = _
  have hInd : iIndepFun (fun i : Fin k => fun rows : Fin n → ReplacementRowPair n d => rows (f i))
      (Measure.pi (fun _ : Fin n => replacementRowPairLaw hn hdn)) :=
    iIndepFun.precomp f.injective (iIndepFun_pi (fun _ => measurable_id.aemeasurable))
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply (f i)).aemeasurable)).mp hInd]
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : Fin n => replacementRowPairLaw hn hdn) (f i)).map_eq

end CircularLaw
