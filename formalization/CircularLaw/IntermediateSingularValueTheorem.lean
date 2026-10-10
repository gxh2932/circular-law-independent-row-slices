import CircularLaw.IntermediateExponentialRadius

/-!
# The full uniform lower-band intermediate-singular-value estimate

The source rounded index is a singular value of the literal full matrix
`M-zeta I`. The checked surviving-row event, inverse-moment counting,
principal Gram comparison, exact index estimates and radius absorption
give one uniform failure bound `B/d` throughout the lower degree band.
-/

noncomputable section
set_option maxHeartbeats 1000000
open Classical Filter
open scoped Topology

namespace CircularLaw

def IntermediateSingularValueEvent {n d : ℕ} (ζ : ℂ) (R : ℝ)
    (rows : RowSliceMatrix n d) : Prop :=
  ∃ h : intermediateDeletionCount n d < n,
    Real.exp (-R * Real.rpow (d : ℝ) (1 / 96)) ≤
      orderedSquareSingularValues (fullShiftedSliceMatrix ζ rows) (intermediateSingularIndex n d h)

theorem survivingRowDistanceEvent_implies_intermediate {n d : ℕ}
    (T : Finset (Fin n)) (hT : T.card = n - kernelCodimension n d)
    (ζ : ℂ) (R : ℝ) (hd : 0 < d) (hIndex : intermediateDeletionCount n d < n)
    (hLog : Real.log (d : ℝ) ≤ Real.rpow (d : ℝ) (1 / 96))
    (rows : RowSliceMatrix n d)
    (h : SurvivingRowDistanceEvent T ζ (Real.exp (-R * Real.rpow (d : ℝ) (1 / 96))) rows) :
    IntermediateSingularValueEvent ζ (R + 1) rows := by
  obtain ⟨H, _, hCard, hDist, _, _⟩ := h
  have hCard' : Fintype.card H = n - kernelCodimension n d - rowDeletionThreshold n d := by
    simpa only [Fintype.card_coe, hT] using hCard
  let i : Fin (Fintype.card H) := ⟨(intermediateSingularIndex n d hIndex).val, by
    rw [hCard']
    exact intermediateSingularIndex_surviving_lt hIndex⟩
  have hTail : Fintype.card H ≤ (Fintype.card H - i.val) * d ^ 2 := by
    change Fintype.card H ≤ (Fintype.card H - (intermediateSingularIndex n d hIndex).val) * d ^ 2
    rw [hCard']
    exact intermediateSingularIndex_tail_degree_bound hd hIndex
  refine ⟨hIndex, (intermediate_radius_div_degree hd R hLog).trans ?_⟩
  exact surviving_rows_square_singular_value_degree_bound H ζ rows (Real.exp_pos _)
    hDist i (intermediateSingularIndex n d hIndex) rfl hd hTail

/-- Full Section 7 conclusion with uniform spectral windows, the literal
rounded deletion count and an explicit `B/d` failure bound. The constants
may be chosen independently of the fixed window; the dimension threshold
depends on that window, sigma and the lower logarithmic constant. -/
def IntermediateSingularValueTheorem : Prop :=
  ∃ Cstar R B : ℝ, 0 < Cstar ∧ 0 < R ∧ 0 < B ∧
    ∀ C : ℝ, Cstar ≤ C → ∀ σ Z₀ : ℝ, 0 < σ → σ < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, InLowerBand C σ n d →
        intermediateDeletionCount n d < n ∧
        (intermediateDeletionCount n d : ℝ) ≤ 5 * ((n : ℝ) / (d : ℝ) ^ 2) ∧
        ∀ ζ : ℂ, ‖ζ‖ ≤ Z₀ * Real.sqrt d →
          1 - B / d ≤ uniformProbability (IntermediateSingularValueEvent (n := n) (d := d) ζ R)

theorem intermediate_singular_value_theorem : IntermediateSingularValueTheorem := by
  obtain ⟨Cstar, R, hCstar, hR, hSurvive⟩ := surviving_row_distance_theorem
  refine ⟨Cstar, R + 1, 2 * R, hCstar, by linarith, by positivity, ?_⟩
  intro C hC σ Z₀ hσ0 hσ1
  obtain ⟨NS, hNS⟩ := hSurvive C hC σ Z₀ hσ0 hσ1
  obtain ⟨NP, hNP⟩ := eventually_atTop.mp
    (eventually_intermediate_singular_parameters (hCstar.trans_le hC) hσ1.le)
  refine ⟨max NS NP, ?_⟩
  intro n hn d hBand
  have hParameters := hNP n ((le_max_right _ _).trans hn) d hBand
  have hd : 0 < d := by have h := hParameters.1; omega
  have hIndex := intermediateDeletionCount_lt_dimension hParameters.1 hParameters.2.1
  refine ⟨hIndex, intermediateDeletionCount_scale_bound hd hParameters.2.1, ?_⟩
  intro ζ hShift
  have hNCard : n - kernelCodimension n d ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Nat.sub_le n (kernelCodimension n d)
  obtain ⟨T, _, hT⟩ := Finset.exists_subset_card_eq hNCard
  apply (hNS n ((le_max_left _ _).trans hn) d hBand T hT ζ hShift).trans
  exact uniformProbability_mono (fun rows h =>
    survivingRowDistanceEvent_implies_intermediate T hT ζ R hd hIndex hParameters.2.2 rows h)

end CircularLaw
