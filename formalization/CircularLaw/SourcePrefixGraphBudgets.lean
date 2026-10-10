import CircularLaw.BernoulliPrefixFiltration
import CircularLaw.SourceExposureUniqueEvents

/-!
# Graph budgets that depend only on the exposed prefix

Square times require the budgets of the square in both orientations;
rectangular times require the budgets of the one-extra-column prefix.
These are functions of the exposed entries. The simultaneous ambient
graph event implies each of them without using that future-dependent
ambient event as the conditioning event.
-/

noncomputable section
open Classical MeasureTheory
open scoped Matrix NNReal

namespace CircularLaw

def SourcePrefixGraphBudget {N a m : ℕ}
    (A : Matrix (Fin a) (Fin m) ℂ) (e : Fin a ↪ Fin m) (β d : ℝ) : Prop :=
  MatrixColumnDegreeBudget A 8 N d ∧
    MatrixUniqueExpansionBudget A e β N d (sourceExposureExpansionSeed N m)
      (sourceGraphTerminalScale N d) ∧ MatrixHeavyRowBudget A β N d

def SourceCurrentPrefixGraphBudget {N a m : ℕ}
    (u : Fin a × Fin m → Bool) (β d : ℝ) : Prop :=
  (∀ hSquare : a = m,
    let A := bernoulliRectangularMatrix
      (fun ij : Fin a × Fin a => u (ij.1, Fin.cast hSquare ij.2))
    SourcePrefixGraphBudget (N := N) A (Function.Embedding.refl _) β d ∧
      SourcePrefixGraphBudget (N := N) A.conjTranspose (Function.Embedding.refl _) β d) ∧
  ∀ hRectangle : m = a + 1,
    SourcePrefixGraphBudget (N := N)
      (bernoulliRectangularMatrix
        (fun ij : Fin a × Fin (a + 1) => u (ij.1, Fin.cast hRectangle.symm ij.2)))
      Fin.castSuccEmb β d

theorem source_global_graph_budget_square_prefix {N m : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) (hm : m ≤ N) {β d : ℝ}
    (hRows : 3 * (N : ℝ) / 4 ≤ m) (hGlobal : BidirectionalSourceExposureGraphBudget A β d) :
    SourcePrefixGraphBudget (N := N) (A.submatrix (Fin.castLE hm) (Fin.castLE hm))
      (Function.Embedding.refl _) β d ∧
    SourcePrefixGraphBudget (N := N)
      (A.submatrix (Fin.castLE hm) (Fin.castLE hm)).conjTranspose
      (Function.Embedding.refl _) β d := by
  let r : Fin m ↪ Fin N := ⟨Fin.castLE hm, Fin.castLE_injective hm⟩
  have hForward := hGlobal.1.1 m m r r
  have hAdjoint := hGlobal.1.2 m m r r
  have hUnique := (hGlobal.2.1 m hm hRows).1
  have hUniqueAdjoint := (hGlobal.2.2 m hm hRows).1
  exact ⟨⟨hForward.1, hUnique, hForward.2⟩,
    ⟨hAdjoint.1, hUniqueAdjoint, hAdjoint.2⟩⟩

theorem source_global_graph_budget_rectangular_prefix {N m : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) (hm : m ≤ N) (hNext : m + 1 ≤ N) {β d : ℝ}
    (hRows : 3 * (N : ℝ) / 4 ≤ m) (hGlobal : BidirectionalSourceExposureGraphBudget A β d) :
    SourcePrefixGraphBudget (N := N) (A.submatrix (Fin.castLE hm) (Fin.castLE hNext))
      Fin.castSuccEmb β d := by
  let r : Fin m ↪ Fin N := ⟨Fin.castLE hm, Fin.castLE_injective hm⟩
  let c : Fin (m + 1) ↪ Fin N := ⟨Fin.castLE hNext, Fin.castLE_injective hNext⟩
  have hDegree := hGlobal.1.1 m (m + 1) r c
  exact ⟨hDegree.1, (hGlobal.2.1 m hm hRows).2 hNext, hDegree.2⟩

theorem source_global_graph_budget_current_prefix {N a m : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (x : BernoulliSquareSample N) {β d : ℝ}
    (hRows : 3 * (N : ℝ) / 4 ≤ a)
    (hGlobal : BidirectionalSourceExposureGraphBudget (bernoulliSquareMatrix x) β d) :
    SourceCurrentPrefixGraphBudget (N := N) (bernoulliPrefixSample ha hm x) β d := by
  constructor
  · intro hSquare
    subst m
    exact source_global_graph_budget_square_prefix (bernoulliSquareMatrix x) ha hRows hGlobal
  · intro hRectangle
    subst m
    exact source_global_graph_budget_rectangular_prefix (bernoulliSquareMatrix x) ha hm hRows hGlobal

theorem measurableSet_source_current_prefix_graph_budget {N a m : ℕ}
    (ha : a ≤ N) (hm : m ≤ N) (β d : ℝ) :
    MeasurableSet[bernoulliPrefixSigmaAlgebra ha hm]
      {x | SourceCurrentPrefixGraphBudget (N := N) (bernoulliPrefixSample ha hm x) β d} :=
  measurableSet_bernoulli_prefix_event ha hm (fun u => SourceCurrentPrefixGraphBudget (N := N) u β d)

end CircularLaw
