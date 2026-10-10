import CircularLaw.LevelPartition

/-!
# Exact refinement of successive canonical approximations

Rounding at the integer multiple `k*d` and then at `k` is exactly the
canonical `k` approximation. Consequently every finer value level lies
inside its corresponding coarse value level. These are the literal floor
identities used in LLTTY19 Lemma 5.9, including negative coordinates.
-/

noncomputable section

namespace CircularLaw

theorem canonical_floor_index_mul (k d : ℕ) (hd : 0 < d) (x : ℝ) :
    ⌊((k * d : ℕ) : ℝ) * x⌋ / (d : ℤ) = ⌊(k : ℝ) * x⌋ := by
  have hMul : ((k * d : ℕ) : ℝ) * x = ((k : ℝ) * x) * (d : ℝ) := by
    push_cast
    ring
  rw [hMul]
  exact Int.mul_natCast_floor_div_cancel hd.ne' ((k : ℝ) * x)

theorem canonical_floor_index_refinement {k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (x : ℝ) :
    ⌊(k : ℝ) * ((⌊((k * d : ℕ) : ℝ) * x⌋ : ℝ) / (k * d : ℕ))⌋ =
      ⌊(k : ℝ) * x⌋ := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hDivide : (k : ℝ) * ((⌊((k * d : ℕ) : ℝ) * x⌋ : ℝ) / (k * d : ℕ)) =
      (⌊((k * d : ℕ) : ℝ) * x⌋ : ℝ) / (d : ℝ) := by
    push_cast
    field_simp
  rw [hDivide, Int.floor_div_natCast, Int.floor_intCast]
  exact canonical_floor_index_mul k d hd x

theorem canonicalApprox_refinement {k d : ℕ} (hk : 0 < k) (hd : 0 < d) (z : ℂ) :
    canonicalApprox k (canonicalApprox (k * d) z) = canonicalApprox k z := by
  apply Complex.ext
  · change (⌊(k : ℝ) * ((⌊((k * d : ℕ) : ℝ) * z.re⌋ : ℝ) / (k * d : ℕ))⌋ : ℝ) /
      (k : ℝ) = (⌊(k : ℝ) * z.re⌋ : ℝ) / (k : ℝ)
    rw [canonical_floor_index_refinement hk hd]
  · change (⌊(k : ℝ) * ((⌊((k * d : ℕ) : ℝ) * z.im⌋ : ℝ) / (k * d : ℕ))⌋ : ℝ) /
      (k : ℝ) = (⌊(k : ℝ) * z.im⌋ : ℝ) / (k : ℝ)
    rw [canonical_floor_index_refinement hk hd]

theorem canonicalApprox_eq_of_finer_eq {k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    {z w : ℂ} (h : canonicalApprox (k * d) z = canonicalApprox (k * d) w) :
    canonicalApprox k z = canonicalApprox k w := by
  simpa only [canonicalApprox_refinement hk hd] using congrArg (canonicalApprox k) h

theorem canonicalApprox_pow_refinement {d : ℕ} (hd : 0 < d) (u : ℕ) (z : ℂ) :
    canonicalApprox (d ^ u) (canonicalApprox (d ^ (u + 1)) z) =
      canonicalApprox (d ^ u) z := by
  rw [pow_succ]
  exact canonicalApprox_refinement (pow_pos hd u) hd z

theorem canonicalApprox_pow_eq_of_finer_eq {d : ℕ} (hd : 0 < d) (u : ℕ)
    {z w : ℂ} (h : canonicalApprox (d ^ (u + 1)) z = canonicalApprox (d ^ (u + 1)) w) :
    canonicalApprox (d ^ u) z = canonicalApprox (d ^ u) w := by
  simpa only [canonicalApprox_pow_refinement hd u] using
    congrArg (canonicalApprox (d ^ u)) h

theorem canonicalApprox_initialLevel_subset {n k d : ℕ} (hk : 0 < k) (hd : 0 < d)
    (x : Fin n → ℂ) (i : Fin n) :
    initialLevel (fun j => canonicalApprox (k * d) (x j)) (canonicalApprox (k * d) (x i)) ⊆
      initialLevel (fun j => canonicalApprox k (x j)) (canonicalApprox k (x i)) := by
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
    canonicalApprox_eq_of_finer_eq hk hd (Finset.mem_filter.mp hj).2⟩

theorem canonicalApprox_pow_initialLevel_subset {n d : ℕ} (hd : 0 < d) (u : ℕ)
    (x : Fin n → ℂ) (i : Fin n) :
    initialLevel (fun j => canonicalApprox (d ^ (u + 1)) (x j))
      (canonicalApprox (d ^ (u + 1)) (x i)) ⊆
      initialLevel (fun j => canonicalApprox (d ^ u) (x j)) (canonicalApprox (d ^ u) (x i)) := by
  rw [pow_succ]
  exact canonicalApprox_initialLevel_subset (pow_pos hd u) hd x i

theorem canonicalApprox_pow_initialLevel_card_le {n d : ℕ} (hd : 0 < d) (u : ℕ)
    (x : Fin n → ℂ) (i : Fin n) :
    (initialLevel (fun j => canonicalApprox (d ^ (u + 1)) (x j))
      (canonicalApprox (d ^ (u + 1)) (x i))).card ≤
      (initialLevel (fun j => canonicalApprox (d ^ u) (x j))
        (canonicalApprox (d ^ u) (x i))).card :=
  Finset.card_le_card (canonicalApprox_pow_initialLevel_subset hd u x i)

end CircularLaw
