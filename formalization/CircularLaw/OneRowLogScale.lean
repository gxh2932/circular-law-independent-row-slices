import CircularLaw.DistanceLogDegreeMoment

/-!
# Trace codimension gives the literal one-row scale and lower mean
-/

noncomputable section
open Classical MeasureTheory
open scoped NNReal ENNReal

namespace CircularLaw

def rowLogComparisonQ (n d r : ℕ) : ℝ :=
  let p := rowBernoulliParameter n d
  (p : ℝ) * (1 - (p : ℝ)) * ((r : ℝ) + 1)

theorem regularizedDistanceScale_ge_sqrt_codimension {n d r : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsPositiveMatrixContraction P)
    (hTrace : (r : ℝ) + 1 ≤ P.trace.re) (η : ℝ) (u : EuclideanSpace ℂ (Fin n)) :
    Real.sqrt (rowLogComparisonQ n d r) ≤
      regularizedDistanceScale P η u (rowBernoulliParameter n d) := by
  let p := rowBernoulliParameter n d
  have hp := rowBernoulliParameter_le_one (show 0 < n by omega) hdn
  have hpR : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hVariance : 0 ≤ (p : ℝ) * (1 - p) := mul_nonneg p.coe_nonneg (by linarith)
  have hQ : 0 ≤ rowLogComparisonQ n d r := by
    dsimp [rowLogComparisonQ]
    exact mul_nonneg hVariance (by positivity)
  have hScale := regularizedDistanceScale_sq hP.1 p hp η u
  have hTraceWeighted := mul_le_mul_of_nonneg_left hTrace hVariance
  have hQuadratic := matrixEuclideanQuadratic_nonneg hP.1 (u + bernoulliMeanVector (Fin n) p)
  have hScaleLower : rowLogComparisonQ n d r ≤ regularizedDistanceScale P η u p ^ 2 := by
    dsimp [regularizedDistanceScaleSq] at hScale
    dsimp [rowLogComparisonQ]
    nlinarith [sq_nonneg η]
  have hScalePos : 0 ≤ regularizedDistanceScale P η u p := Real.sqrt_nonneg _
  have hRoot := Real.sqrt_nonneg (rowLogComparisonQ n d r)
  have hRootSq := Real.sq_sqrt hQ
  change Real.sqrt (rowLogComparisonQ n d r) ≤ regularizedDistanceScale P η u p
  nlinarith

theorem regularizedDistanceMean_ge_sqrt_codimension_eighth {n d r : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsPositiveMatrixContraction P)
    (hTrace : (r : ℝ) + 1 ≤ P.trace.re) (η : ℝ) (u : EuclideanSpace ℂ (Fin n))
    (hQ : 1 ≤ rowLogComparisonQ n d r) :
    Real.sqrt (rowLogComparisonQ n d r) / 8 ≤
      regularizedDistanceMean P η u (rowBernoulliParameter n d)
        (rowBernoulliParameter_le_one (by omega) hdn) := by
  have hScale := regularizedDistanceScale_ge_sqrt_codimension hd hdn hP hTrace η u
  have hRoot : 1 ≤ Real.sqrt (rowLogComparisonQ n d r) := Real.one_le_sqrt.mpr hQ
  have hMean := regularizedDistanceMean_ge_scale_eighth hP (rowBernoulliParameter n d)
    (rowBernoulliParameter_le_one (by omega) hdn) η u (hRoot.trans hScale)
  linarith

end CircularLaw
