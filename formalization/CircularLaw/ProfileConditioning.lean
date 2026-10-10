import CircularLaw.ProfileEstimator
import CircularLaw.FiniteConditioning

/-!
# The exact row law conditional on profile counts

Conditioning on counts does not make the original ordered coordinate samples
independent. Instead, their sum has the law of independent uniform samples
inside each part. We establish that representation with a finite equivalence:
the count fiber is a label-assignment space times the product of block samples.
-/

noncomputable section
open scoped BigOperators

namespace CircularLaw

def rowLabels {α ι : Type*} (part : α → ι) {d : ℕ} (samples : Fin d → α) : Fin d → ι :=
  fun i => part (samples i)

def profileCounts {α ι : Type*} (part : α → ι) {d : ℕ} (samples : Fin d → α) : ι → ℕ :=
  fun q => trialCount (fun a => part a = q) samples

theorem trialCount_le_degree {α : Type*} (P : α → Prop) {d : ℕ} (samples : Fin d → α) :
    trialCount P samples ≤ d := by
  classical
  simpa only [trialCount, Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.filter_subset (fun i => P (samples i)) Finset.univ)

def boundedProfileCounts {α ι : Type*} (part : α → ι) {d : ℕ} (samples : Fin d → α) :
    ι → Fin (d + 1) :=
  fun q => ⟨profileCounts part samples q, Nat.lt_succ_of_le (trialCount_le_degree _ samples)⟩

theorem boundedProfileCounts_eq_iff {α ι : Type*} (part : α → ι) {d : ℕ} (s t : Fin d → α) :
    boundedProfileCounts part s = boundedProfileCounts part t ↔
      profileCounts part s = profileCounts part t := by
  constructor
  · intro h
    funext q
    exact congrArg Fin.val (congrFun h q)
  · intro h
    funext q
    apply Fin.ext
    exact congrFun h q

abbrev ProfileFiber {α ι : Type*} (part : α → ι) (d : ℕ) (Q : ι → ℕ) :=
  {samples : Fin d → α // profileCounts part samples = Q}

abbrev LabelProfileFiber {ι : Type*} (d : ℕ) (Q : ι → ℕ) :=
  {labels : Fin d → ι // profileCounts id labels = Q}

abbrev RowLabelFiber {α ι : Type*} (part : α → ι) {d : ℕ} (labels : Fin d → ι) :=
  {samples : Fin d → α // rowLabels part samples = labels}

abbrev ProfileBlocks {α ι : Type*} (part : α → ι) (Q : ι → ℕ) :=
  ∀ q, Fin (Q q) → {a : α // part a = q}

def boundedProfileFiberEquiv {α ι : Type*} (part : α → ι) {d : ℕ} (reference : Fin d → α) :
    {samples : Fin d → α // boundedProfileCounts part samples = boundedProfileCounts part reference} ≃
      ProfileFiber part d (profileCounts part reference) :=
  Equiv.subtypeEquivRight (fun samples => boundedProfileCounts_eq_iff part samples reference)

theorem profileCounts_labels {α ι : Type*} (part : α → ι) {d : ℕ} (samples : Fin d → α) :
    profileCounts id (rowLabels part samples) = profileCounts part samples := rfl

def profileIndexEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} {Q : ι → ℕ}
    (labels : LabelProfileFiber d Q) (q : ι) :
    {i : Fin d // labels.val i = q} ≃ Fin (Q q) := by
  classical
  apply Fintype.equivFinOfCardEq
  have h := congrFun labels.property q
  rw [← h]
  unfold profileCounts trialCount
  rw [Fintype.card_subtype]
  congr 1
  ext i
  simp

def rowLabelPiEquiv {α ι : Type*} (part : α → ι) {d : ℕ} (labels : Fin d → ι) :
    RowLabelFiber part labels ≃ (∀ i, {a : α // part a = labels i}) :=
  (Equiv.subtypeEquivRight (p := fun samples => rowLabels part samples = labels)
    (q := fun samples => ∀ i, part (samples i) = labels i) (fun _ => funext_iff)).trans
      (Equiv.subtypePiEquivPi (p := fun i a => part a = labels i))

def labelBlockEquiv {α ι : Type*} [Fintype ι] [DecidableEq ι] (part : α → ι)
    {d : ℕ} {Q : ι → ℕ} (labels : LabelProfileFiber d Q) (q : ι) :
    (∀ i : {i : Fin d // labels.val i = q}, {a : α // part a = labels.val i.val}) ≃
      (Fin (Q q) → {a : α // part a = q}) :=
  (Equiv.piCongrRight (fun i => Equiv.subtypeEquivRight (fun _ => by rw [i.property]))).trans
    (Equiv.piCongrLeft (fun _ : Fin (Q q) => {a : α // part a = q}) (profileIndexEquiv labels q))

def rowLabelBlocksEquiv {α ι : Type*} [Fintype ι] [DecidableEq ι] (part : α → ι)
    {d : ℕ} {Q : ι → ℕ} (labels : LabelProfileFiber d Q) :
    RowLabelFiber part labels.val ≃ ProfileBlocks part Q :=
  (rowLabelPiEquiv part labels.val).trans (Equiv.piCongrFiberwise (labelBlockEquiv part labels))

theorem rowLabelBlocksEquiv_apply_val {α ι : Type*} [Fintype ι] [DecidableEq ι] (part : α → ι)
    {d : ℕ} {Q : ι → ℕ} (labels : LabelProfileFiber d Q)
    (samples : RowLabelFiber part labels.val) (q : ι) (j : Fin (Q q)) :
    ((rowLabelBlocksEquiv part labels samples) q j).val =
      samples.val ((profileIndexEquiv labels q).symm j).val := by
  simp [rowLabelBlocksEquiv, rowLabelPiEquiv, labelBlockEquiv, Equiv.piCongrFiberwise_apply,
    Equiv.piCongrLeft_apply, Equiv.piCongrRight_apply]
  rfl

def profileFiberEquiv {α ι : Type*} [Fintype ι] [DecidableEq ι] (part : α → ι)
    (d : ℕ) (Q : ι → ℕ) :
    ProfileFiber part d Q ≃ LabelProfileFiber d Q × ProfileBlocks part Q :=
  (Equiv.sigmaSubtypeFiberEquivSubtype (rowLabels part)
    (p := fun samples => profileCounts part samples = Q)
    (q := fun labels => profileCounts id labels = Q) (fun _ => Iff.rfl)).symm.trans
      ((Equiv.sigmaCongrRight (rowLabelBlocksEquiv part)).trans
        (Equiv.sigmaEquivProd (LabelProfileFiber d Q) (ProfileBlocks part Q)))

def profileBlockSum {α ι : Type*} [Fintype ι] (y : α → ℂ) {part : α → ι} {Q : ι → ℕ}
    (blocks : ProfileBlocks part Q) : ℂ := ∑ q, ∑ a, y (blocks q a).val

theorem rowLabelBlocksEquiv_sum {α ι : Type*} [Fintype ι] [DecidableEq ι] (part : α → ι)
    {d : ℕ} {Q : ι → ℕ} (labels : LabelProfileFiber d Q)
    (samples : RowLabelFiber part labels.val) (y : α → ℂ) :
    (∑ i, y (samples.val i)) = profileBlockSum y (rowLabelBlocksEquiv part labels samples) := by
  classical
  have hf : (∑ i, y (samples.val i)) =
      ∑ q, ∑ i : {i : Fin d // labels.val i = q}, y (samples.val i.val) := by
    rw [← (Equiv.sigmaFiberEquiv labels.val).sum_comp (fun i => y (samples.val i)), Fintype.sum_sigma]
    rfl
  rw [hf]
  unfold profileBlockSum
  apply Finset.sum_congr rfl
  intro q _
  apply Fintype.sum_equiv (profileIndexEquiv labels q)
  intro i
  rw [rowLabelBlocksEquiv_apply_val, Equiv.symm_apply_apply]

theorem profileFiberEquiv_sum {α ι : Type*} [Fintype ι] [DecidableEq ι] (part : α → ι)
    {d : ℕ} {Q : ι → ℕ} (samples : ProfileFiber part d Q) (y : α → ℂ) :
    (∑ i, y (samples.val i)) = profileBlockSum y (profileFiberEquiv part d Q samples).2 := by
  exact rowLabelBlocksEquiv_sum part
    ⟨rowLabels part samples.val, samples.property⟩ ⟨samples.val, rfl⟩ y

/-- Equation (conditional-block-sum) with the exact finite conditional law.
Only a realized profile is required. The label-assignment multiplicity cancels
because the linear sum does not depend on the label ordering. -/
theorem conditional_profile_blocks_law {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (part : α → ι) {d : ℕ} {Q : ι → ℕ} (hQ : Nonempty (ProfileFiber part d Q))
    (E : ProfileBlocks part Q → Prop) :
    uniformProbability (fun samples : ProfileFiber part d Q => E (profileFiberEquiv part d Q samples).2) =
      uniformProbability E := by
  classical
  have hlabels : Nonempty (LabelProfileFiber d Q) := by
    rcases hQ with ⟨samples⟩
    exact ⟨⟨rowLabels part samples.val, samples.property⟩⟩
  letI := hlabels
  rw [← finiteMean_indicator]
  rw [finiteMean_reindex (profileFiberEquiv part d Q)
    (fun p : LabelProfileFiber d Q × ProfileBlocks part Q => if E p.2 then (1 : ℝ) else 0)]
  rw [finiteMean_snd (fun blocks : ProfileBlocks part Q => if E blocks then (1 : ℝ) else 0),
    finiteMean_indicator]

theorem conditional_profile_sum_law {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (part : α → ι) {d : ℕ} {Q : ι → ℕ} (hQ : Nonempty (ProfileFiber part d Q))
    (y : α → ℂ) (E : ℂ → Prop) :
    uniformProbability (fun samples : ProfileFiber part d Q => E (∑ i, y (samples.val i))) =
      uniformProbability (fun blocks : ProfileBlocks part Q => E (profileBlockSum y blocks)) := by
  classical
  have he : (fun samples : ProfileFiber part d Q => E (∑ i, y (samples.val i))) =
      (fun samples => E (profileBlockSum y (profileFiberEquiv part d Q samples).2)) :=
    funext (fun samples => congrArg E (profileFiberEquiv_sum part samples y))
  rw [he]
  exact conditional_profile_blocks_law part hQ
    (fun blocks : ProfileBlocks part Q => E (profileBlockSum y blocks))

/-- The block representation has independent uniform coordinates inside
each part, as well as independence between parts. -/
theorem conditional_profile_independent_samples {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (part : α → ι) {d : ℕ} {Q : ι → ℕ} (hQ : Nonempty (ProfileFiber part d Q))
    (E : ∀ q, Fin (Q q) → {a : α // part a = q} → Prop) :
    uniformProbability (fun samples : ProfileFiber part d Q =>
      ∀ q a, E q a ((profileFiberEquiv part d Q samples).2 q a)) =
        ∏ q, ∏ a, uniformProbability (E q a) := by
  classical
  rw [conditional_profile_blocks_law part hQ
    (fun blocks : ProfileBlocks part Q => ∀ q a, E q a (blocks q a))]
  calc
    _ = ∏ q, uniformProbability (fun b : Fin (Q q) → {a : α // part a = q} =>
        ∀ a, E q a (b a)) := uniformProbability_pi
          (fun q => fun b : Fin (Q q) → {a : α // part a = q} => ∀ a, E q a (b a))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro q _
      exact uniformProbability_pi (E q)

theorem conditional_profile_sum_le_block {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (part : α → ι) {d : ℕ} {Q : ι → ℕ} (hQ : Nonempty (ProfileFiber part d Q))
    (y : α → ℂ) (q : ι) {r A : ℝ}
    (hq : ∀ z : ℂ, uniformProbability (fun b : Fin (Q q) → {a : α // part a = q} =>
      ‖(∑ a, y (b a).val) - z‖ ≤ r) ≤ A) (z : ℂ) :
    uniformProbability (fun samples : ProfileFiber part d Q =>
      ‖(∑ i, y (samples.val i)) - z‖ ≤ r) ≤ A := by
  classical
  rcases hQ with ⟨samples⟩
  letI : ∀ q, Nonempty (Fin (Q q) → {a : α // part a = q}) :=
    fun q => ⟨(profileFiberEquiv part d Q samples).2 q⟩
  rw [conditional_profile_sum_law part ⟨samples⟩ y (fun w : ℂ => ‖w - z‖ ≤ r)]
  exact uniformProbability_pi_sum_small_ball
    (β := fun q => Fin (Q q) → {a : α // part a = q})
    (fun q (b : Fin (Q q) → {a : α // part a = q}) => ∑ a, y (b a).val) q hq z

theorem visitedParts_eq_of_counts {α ι : Type*} (part : α → ι) {d : ℕ}
    (s t : Fin d → α) (h : profileCounts part s = profileCounts part t) :
    visitedParts part s = visitedParts part t := by
  classical
  ext q
  rw [mem_visitedParts_iff, mem_visitedParts_iff]
  have hq := congrFun h q
  change trialCount (fun a => part a = q) s = trialCount (fun a => part a = q) t at hq
  rw [hq]

/-- The actual estimator is a function of the profile counts, as required
when averaging its conditional bound. -/
theorem actualProfileEstimator_eq_of_counts {α ι : Type*} (P : RowProfile α ι)
    {d : ℕ} (hd : 0 < d) (s t : Fin d → α) (h : profileCounts P.part s = profileCounts P.part t) :
    profileEstimator P.part (actualProfileWeight P s) hd s =
      profileEstimator P.part (actualProfileWeight P t) hd t := by
  classical
  have hw : actualProfileWeight P s = actualProfileWeight P t := by
    funext q
    have hq := congrFun h q
    change trialCount (fun a => P.part a = q) s = trialCount (fun a => P.part a = q) t at hq
    simp only [actualProfileWeight, hq]
  rw [profileEstimator_eq_visited_min P.part (actualProfileWeight P s) hd s,
    profileEstimator_eq_visited_min P.part (actualProfileWeight P t) hd t, hw]
  congr 1
  exact Finset.inf'_congr _ (visitedParts_eq_of_counts P.part s t h) (fun _ _ => rfl)

/-- Assemble the conditional row estimator from the geometric block
concentration bounds. Those bounds remain explicit proof obligations; this
theorem does not assume the full row-local lemma or name it as an axiom. -/
theorem conditional_profile_estimator_of_block_bounds {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] (P : RowProfile α ι)
    {d : ℕ} (hd : 0 < d) (reference : Fin d → α) (y : α → ℂ) {r K : ℝ} (hK : 1 ≤ K)
    (hblock : ∀ q, 0 < profileCounts P.part reference q → ∀ z : ℂ,
      uniformProbability (fun b : Fin (profileCounts P.part reference q) → {a : α // P.part a = q} =>
        ‖(∑ a, y (b a).val) - z‖ ≤ r) ≤ K * (actualProfileWeight P reference q)⁻¹) (z : ℂ) :
    uniformProbability (fun samples : ProfileFiber P.part d (profileCounts P.part reference) =>
      ‖(∑ i, y (samples.val i)) - z‖ ≤ r) ≤
        K * profileEstimator P.part (actualProfileWeight P reference) hd reference := by
  classical
  change _ ≤ K * min 1 (Finset.univ.inf' _
    (fun i => (actualProfileWeight P reference (P.part (reference i)))⁻¹))
  rw [mul_min_of_nonneg _ _ (by linarith : 0 ≤ K)]
  apply le_min
  · exact (uniformProbability_le_one _).trans (by simpa only [mul_one] using hK)
  · rcases Finset.exists_mem_eq_inf'
      (⟨⟨0, hd⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin d)).Nonempty)
      (fun i => (actualProfileWeight P reference (P.part (reference i)))⁻¹) with ⟨i, _, hi⟩
    rw [hi]
    exact conditional_profile_sum_le_block P.part ⟨⟨reference, rfl⟩⟩ y (P.part (reference i))
      (hblock _ (trialCount_pos_of_sample P.part reference i)) z

/-- Average the exact conditional row estimator. The geometric concentration
estimate for each visited part remains an explicit argument. -/
theorem averaged_row_small_ball_of_block_bounds {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] (P : RowProfile α ι)
    {d : ℕ} (hd : 0 < d) (y : α → ℂ) {r K : ℝ} (hK : 1 ≤ K)
    (hblock : ∀ reference : Fin d → α, ∀ q, 0 < profileCounts P.part reference q → ∀ z : ℂ,
      uniformProbability (fun b : Fin (profileCounts P.part reference q) → {a : α // P.part a = q} =>
        ‖(∑ a, y (b a).val) - z‖ ≤ r) ≤ K * (actualProfileWeight P reference q)⁻¹) (z : ℂ) :
    uniformProbability (fun samples : Fin d → α => ‖(∑ i, y (samples i)) - z‖ ≤ r) ≤
      K * finiteMean (fun samples => profileEstimator P.part (actualProfileWeight P samples) hd samples) := by
  classical
  rw [← finiteMean_const_mul]
  apply uniformProbability_le_fiber_reference (boundedProfileCounts P.part)
    (fun samples : Fin d → α => ‖(∑ i, y (samples i)) - z‖ ≤ r)
    (fun samples => K * profileEstimator P.part (actualProfileWeight P samples) hd samples)
  · intro s t h
    rw [actualProfileEstimator_eq_of_counts P hd s t ((boundedProfileCounts_eq_iff P.part s t).mp h)]
  · intro reference
    have h := conditional_profile_estimator_of_block_bounds P hd reference y hK (hblock reference) z
    have he := uniformProbability_reindex (boundedProfileFiberEquiv P.part reference)
      (fun samples : ProfileFiber P.part d (profileCounts P.part reference) =>
        ‖(∑ i, y (samples.val i)) - z‖ ≤ r)
    exact he.trans_le h

/-- The represented sum is the bilinear row action of the actual
with-replacement matrix, not a substituted random observable. -/
theorem withReplacementMatrix_mulVec {n d K : ℕ} (samples : OrderedRows n d K)
    (y : Fin n → ℂ) (i : Fin K) :
    (withReplacementMatrix samples).mulVec y i = ∑ a, y (samples i a) := by
  classical
  unfold Matrix.mulVec dotProduct withReplacementMatrix
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end CircularLaw
