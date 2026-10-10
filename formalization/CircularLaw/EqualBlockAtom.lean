import CircularLaw.UniformSumConcentration

/-!
# A singleton witness in two equal separated blocks

Uniform sampling from two disjoint halves of equal positive size gives
each half probability one half. If coefficient values from opposite
halves are farther apart than twice the radius, a closed disk meets at
most one half. The resulting concentration estimate is center invariant.
-/

noncomputable section

namespace CircularLaw

def subFinsetFiberEquiv {α : Type*} [DecidableEq α] (A B : Finset α) (hAB : A ⊆ B) :
    {a : {x : α // x ∈ B} // a.val ∈ A} ≃ {x : α // x ∈ A} where
  toFun a := ⟨a.val.val, a.property⟩
  invFun a := ⟨⟨a.val, hAB a.property⟩, a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem uniformProbability_union_left {α : Type*} [DecidableEq α] (L R : Finset α)
    (hDis : Disjoint L R) (hEq : L.card = R.card) (hL : L.Nonempty) :
    uniformProbability (fun a : {x : α // x ∈ L ∪ R} => a.val ∈ L) = 1 / 2 := by
  unfold uniformProbability
  rw [Nat.card_congr (subFinsetFiberEquiv L (L ∪ R) (Finset.subset_union_left))]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_union_of_disjoint hDis, ← hEq]
  have hCard : (0 : ℝ) < L.card := by exact_mod_cast Finset.card_pos.mpr hL
  push_cast
  field_simp
  ring

theorem uniformProbability_union_right {α : Type*} [DecidableEq α] (L R : Finset α)
    (hDis : Disjoint L R) (hEq : L.card = R.card) (hL : L.Nonempty) :
    uniformProbability (fun a : {x : α // x ∈ L ∪ R} => a.val ∈ R) = 1 / 2 := by
  unfold uniformProbability
  rw [Nat.card_congr (subFinsetFiberEquiv R (L ∪ R) (Finset.subset_union_right))]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_union_of_disjoint hDis, hEq]
  have hCard : (0 : ℝ) < R.card := by exact_mod_cast (hEq ▸ Finset.card_pos.mpr hL)
  push_cast
  field_simp
  ring

theorem equal_halves_small_ball {α : Type*} [DecidableEq α] (L R : Finset α)
    (hDis : Disjoint L R) (hEq : L.card = R.card) (hL : L.Nonempty)
    (Y : α → ℂ) {r : ℝ}
    (hSep : ∀ a ∈ L, ∀ b ∈ R, 2 * r < dist (Y a) (Y b)) (z : ℂ) :
    uniformProbability (fun a : {x : α // x ∈ L ∪ R} => ‖Y a.val - z‖ ≤ r) ≤ 1 / 2 := by
  classical
  by_cases hLeft : ∃ a ∈ L, ‖Y a - z‖ ≤ r
  · obtain ⟨a, ha, hBall⟩ := hLeft
    have hEvent : ∀ b : {x : α // x ∈ L ∪ R}, ‖Y b.val - z‖ ≤ r → b.val ∈ L := by
      intro b hb
      rcases Finset.mem_union.mp b.property with hbL | hbR
      · exact hbL
      · have hDistance : dist (Y a) (Y b.val) ≤ 2 * r := by
          have h₁ : dist (Y a) z ≤ r := by simpa only [dist_eq_norm] using hBall
          have h₂ : dist z (Y b.val) ≤ r := by simpa only [dist_comm z, dist_eq_norm] using hb
          exact (dist_triangle _ _ _).trans (by linarith)
        exact False.elim ((not_le_of_gt (hSep a ha b.val hbR)) hDistance)
    exact (uniformProbability_mono hEvent).trans_eq
      (uniformProbability_union_left L R hDis hEq hL)
  · have hEvent : ∀ b : {x : α // x ∈ L ∪ R}, ‖Y b.val - z‖ ≤ r → b.val ∈ R := by
      intro b hb
      rcases Finset.mem_union.mp b.property with hbL | hbR
      · exact False.elim (hLeft ⟨b.val, hbL, hb⟩)
      · exact hbR
    exact (uniformProbability_mono hEvent).trans_eq
      (uniformProbability_union_right L R hDis hEq hL)

theorem norm_gap_implies_equal_block_separation {a b : ℂ} {r : ℝ}
    (hGap : 2 * r + ‖b‖ < ‖a‖) : 2 * r < dist a b := by
  rw [dist_eq_norm]
  have h := norm_sub_norm_le a b
  linarith

end CircularLaw
