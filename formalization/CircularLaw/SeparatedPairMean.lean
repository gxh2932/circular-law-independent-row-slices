import CircularLaw.UniformEmbeddingMarginal
import CircularLaw.PairedSliceSmallBall
import CircularLaw.InvertibilityDistanceGeometry
import CircularLaw.Hypergeometric

/-!
# The actual expected number of separated sampled pairs

The coordinate-level-set condition gives a lower bound for two uniform
coordinates. Conditioning them to be distinct can only increase this
probability at positive separation radius. Exact embedding marginals
then give the corresponding mean bound for all sampled pairs.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace CircularLaw

def boolEmbeddingDistinctPairEquiv {α : Type*} :
    (Bool ↪ α) ≃ {p : α × α // p.1 ≠ p.2} where
  toFun e := ⟨(e false, e true), fun h => Bool.false_ne_true (e.injective h)⟩
  invFun p := ⟨fun b => cond b p.val.2 p.val.1, by
    intro b c h
    have hne := p.property
    cases b <;> cases c <;> simp_all⟩
  left_inv e := by ext b; cases b <;> rfl
  right_inv p := by rfl

theorem uniform_distinct_pair_separation_ge {n : ℕ} (hn : 2 ≤ n)
    (y : Fin n → ℂ) {δ ρ : ℝ} (hρ : 0 < ρ)
    (hLevel : ∀ c : ℂ, ((Finset.univ.filter (fun j => ‖y j - c‖ ≤ ρ)).card : ℝ) ≤
      (1 - δ) * n) :
    δ ≤ uniformProbability (fun e : Bool ↪ Fin n => ρ ≤ ‖y (e true) - y (e false)‖) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hSingle (a : Fin n) : δ ≤ uniformProbability (fun b : Fin n => ρ ≤ ‖y b - y a‖) := by
    have hCard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun b => ‖y b - y a‖ ≤ ρ)
    simp only [not_le, Finset.card_univ, Fintype.card_fin] at hCard
    have hCast := congrArg (fun k : ℕ => (k : ℝ)) hCard
    simp only [Nat.cast_add] at hCast
    have hFar : δ * n ≤ ((Finset.univ.filter (fun b => ρ < ‖y b - y a‖)).card : ℝ) := by
      linarith [hLevel (y a)]
    have hStrict : δ ≤ uniformProbability (fun b : Fin n => ρ < ‖y b - y a‖) := by
      rw [uniformProbability, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_fin, Fintype.card_subtype]
      exact (le_div_iff₀ hnR).mpr hFar
    exact hStrict.trans (uniformProbability_mono (fun _ h => h.le))
  have hIndependent : δ ≤ uniformProbability
      (fun p : Fin n × Fin n => ρ ≤ ‖y p.1 - y p.2‖) := by
    rw [uniformProbability_prod_fubini]
    calc
      _ = finiteMean (fun _ : Fin n => δ) := (finiteMean_const δ).symm
      _ ≤ _ := finiteMean_mono hSingle
  let D : Fin n × Fin n → Prop := fun p => p.1 ≠ p.2
  haveI : Nonempty {p : Fin n × Fin n // D p} :=
    ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [D, Fin.mk.injEq]⟩⟩
  have hD : 0 < Nat.card {p : Fin n × Fin n // D p} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  have hProbD : 0 < uniformProbability D := uniformProbability_pos_of_card_pos D hD
  have hFarDistinct (p : Fin n × Fin n) (h : ρ ≤ ‖y p.1 - y p.2‖) : D p := by
    intro heq
    rw [heq, sub_self, norm_zero] at h
    exact (not_le.mpr hρ) h
  have hIntersect : (fun p : Fin n × Fin n => D p ∧ ρ ≤ ‖y p.1 - y p.2‖) =
      (fun p => ρ ≤ ‖y p.1 - y p.2‖) := by
    funext p
    exact propext ⟨And.right, fun h => ⟨hFarDistinct p h, h⟩⟩
  have hCondition := uniformProbability_conditioning D
    (fun p => ρ ≤ ‖y p.1 - y p.2‖) hD
  rw [hIntersect] at hCondition
  have hTransport := uniformProbability_reindex (boolEmbeddingDistinctPairEquiv (α := Fin n))
    (fun p => ρ ≤ ‖y p.val.1 - y p.val.2‖)
  change uniformProbability (fun e : Bool ↪ Fin n => ρ ≤ ‖y (e false) - y (e true)‖) = _
    at hTransport
  have hRev : (fun e : Bool ↪ Fin n => ρ ≤ ‖y (e false) - y (e true)‖) =
      (fun e => ρ ≤ ‖y (e true) - y (e false)‖) := by
    funext e
    rw [norm_sub_rev]
  rw [hRev] at hTransport
  rw [hTransport, hCondition]
  exact hIndependent.trans (le_div_self (uniformProbability_nonneg _)
    hProbD (uniformProbability_le_one D))

def sampledPairDomainEmbedding {d : ℕ} (j : Fin d) : Bool ↪ Fin d ⊕ Fin d where
  toFun b := cond b (Sum.inr j) (Sum.inl j)
  inj' := by intro b c h; cases b <;> cases c <;> simp_all

theorem paired_separated_coordinates_cast_sum {n d : ℕ} (y : Fin n → ℂ) (ρ : ℝ)
    (e : Fin d ⊕ Fin d ↪ Fin n) :
    ((pairedSeparatedCoordinates y ρ e).card : ℝ) =
      ∑ j, if ρ ≤ ‖y (e (Sum.inr j)) - y (e (Sum.inl j))‖ then (1 : ℝ) else 0 := by
  simp only [pairedSeparatedCoordinates, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem separated_pair_count_mean_ge {n d : ℕ} (hSize : 2 * d ≤ n)
    (y : Fin n → ℂ) {δ ρ : ℝ} (hρ : 0 < ρ)
    (hLevel : ∀ c : ℂ, ((Finset.univ.filter (fun j => ‖y j - c‖ ≤ ρ)).card : ℝ) ≤
      (1 - δ) * n) :
    δ * d ≤ finiteMean (fun e : Fin d ⊕ Fin d ↪ Fin n =>
      ((pairedSeparatedCoordinates y ρ e).card : ℝ)) := by
  simp_rw [paired_separated_coordinates_cast_sum]
  rw [finiteMean_finset_sum]
  calc
    _ = ∑ _j : Fin d, δ := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      have hMean := finiteMean_embedding_restriction (sampledPairDomainEmbedding j)
        (by simpa only [Fintype.card_sum, Fintype.card_fin] using
          (by omega : d + d ≤ n))
        (fun e : Bool ↪ Fin n => if ρ ≤ ‖y (e true) - y (e false)‖ then (1 : ℝ) else 0)
      change finiteMean (fun e : Fin d ⊕ Fin d ↪ Fin n =>
        if ρ ≤ ‖y (e (Sum.inr j)) - y (e (Sum.inl j))‖ then (1 : ℝ) else 0) = _ at hMean
      rw [hMean, finiteMean_indicator]
      exact uniform_distinct_pair_separation_ge (by have := j.isLt; omega) y hρ hLevel

theorem source_nonalmost_separated_pair_mean_ge {n d : ℕ} (hSize : 2 * d ≤ n)
    {δ ρ : ℝ} (hρ : 0 < ρ) (x : EuclideanSpace ℂ (Fin n))
    (hx : sourceNonAlmostConstant δ ρ x) :
    δ * d ≤ finiteMean (fun e : Fin d ⊕ Fin d ↪ Fin n =>
      ((pairedSeparatedCoordinates (fun j => x j) (ρ / Real.sqrt n) e).card : ℝ)) := by
  by_cases hd : d = 0
  · subst d
    simp [pairedSeparatedCoordinates, finiteMean]
  · apply separated_pair_count_mean_ge hSize _ (div_pos hρ (Real.sqrt_pos.mpr (by
        exact_mod_cast (by omega : 0 < n))))
    exact hx

end CircularLaw
