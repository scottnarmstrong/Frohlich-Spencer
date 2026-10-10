/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGFreeze
public import FroehlichSpencer.BKT.Charges.BasicLemmaIdentity
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryPairing

/-!
Running the scale-ordered selection with FS81's (2.13) four-branch rewrite
(`chargeFactorProduct_pairBranches_identity`: weights `1/3, 1/3, 1/6, 1/6`, coefficients `3K₁`,
`3K₂`, `3K₁K₂`) gives a finite convex expansion of the charge-factor product of a pinned ensemble
of single sites, **every terminal ensemble of which has the Appendix D geometry**
(`exists_selectionExpansion_of_singleSites`).

Every pair the selection rewrites is an Appendix D conflict at threshold `2M`
(`SelectionState.pairConflict`), so the scheme is the source's conflict pairing with a modified
order (scale-ordered, with freezing) and a constant-factor threshold.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

open FroehlichSpencer.BKT

variable {L : ℕ}

/-- A branch: a weight, a terminal ensemble and its coefficient function. -/
abbrev Branch (L : ℕ) := ℝ × ChargeEnsemble L × (ChargeDensity L → ℝ)

/-- The weighted sum of the charge-factor products of the branches. -/
def branchSum (B : List (Branch L)) (ψ : (Fin L × Fin L) → ℝ) : ℝ :=
  (B.map fun b => b.1 * chargeFactorProduct b.2.1 b.2.2 ψ).sum

/-- The total weight of the branches. -/
def branchMass (B : List (Branch L)) : ℝ := (B.map fun b => b.1).sum

/-- Rescale the weights of a branch family. -/
def scaleBranches (w : ℝ) (B : List (Branch L)) : List (Branch L) :=
  B.map fun b => (w * b.1, b.2)

theorem branchSum_scale (w : ℝ) (B : List (Branch L)) (ψ : (Fin L × Fin L) → ℝ) :
    branchSum (scaleBranches w B) ψ = w * branchSum B ψ := by
  simp only [branchSum, scaleBranches, List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro b _
  simp [mul_assoc]

theorem branchMass_scale (w : ℝ) (B : List (Branch L)) :
    branchMass (scaleBranches w B) = w * branchMass B := by
  simp only [branchMass, scaleBranches, List.map_map]
  rw [← List.sum_map_mul_left]
  rfl

theorem branchSum_append (B C : List (Branch L)) (ψ : (Fin L × Fin L) → ℝ) :
    branchSum (B ++ C) ψ = branchSum B ψ + branchSum C ψ := by
  simp [branchSum]

theorem branchMass_append (B C : List (Branch L)) :
    branchMass (B ++ C) = branchMass B + branchMass C := by
  simp [branchMass]

/-- A **selection expansion** of `∏_{ρ ∈ E} (1 + K(ρ) cos ⟨ψ, ρ⟩)`: a finite convex combination of
the charge-factor products of terminal ensembles, each with the Appendix D geometry. -/
def IsSelectionExpansion (M α : ℝ) (E : ChargeEnsemble L) (K : ChargeDensity L → ℝ)
    (B : List (Branch L)) : Prop :=
  (∀ b ∈ B, 0 < b.1 ∧ AppendixDChargeGeometry M α b.2.1) ∧ branchMass B = 1 ∧
    ∀ ψ, chargeFactorProduct E K ψ = branchSum B ψ

theorem IsSelectionExpansion.combine {M α : ℝ} {E E₁ E₂ E₃ E₄ : ChargeEnsemble L}
    {K K₁ K₂ K₃ K₄ : ChargeDensity L → ℝ} {B₁ B₂ B₃ B₄ : List (Branch L)}
    (h₁ : IsSelectionExpansion M α E₁ K₁ B₁) (h₂ : IsSelectionExpansion M α E₂ K₂ B₂)
    (h₃ : IsSelectionExpansion M α E₃ K₃ B₃) (h₄ : IsSelectionExpansion M α E₄ K₄ B₄)
    (hid : ∀ ψ, chargeFactorProduct E K ψ =
      (1 / 3 : ℝ) * chargeFactorProduct E₁ K₁ ψ + (1 / 3 : ℝ) * chargeFactorProduct E₂ K₂ ψ +
        (1 / 6 : ℝ) * chargeFactorProduct E₃ K₃ ψ + (1 / 6 : ℝ) * chargeFactorProduct E₄ K₄ ψ) :
    IsSelectionExpansion M α E K
      (scaleBranches (1 / 3) B₁ ++ scaleBranches (1 / 3) B₂ ++ scaleBranches (1 / 6) B₃ ++
        scaleBranches (1 / 6) B₄) := by
  refine ⟨fun b hb => ?_, ?_, fun ψ => ?_⟩
  · have mem : ∀ {w : ℝ} {B : List (Branch L)}, 0 < w → (∀ b ∈ B, 0 < b.1 ∧
        AppendixDChargeGeometry M α b.2.1) → b ∈ scaleBranches w B →
        0 < b.1 ∧ AppendixDChargeGeometry M α b.2.1 := by
      intro w B hw hB hb
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      exact ⟨mul_pos hw (hB b' hb').1, (hB b' hb').2⟩
    simp only [List.mem_append] at hb
    rcases hb with ((hb | hb) | hb) | hb
    · exact mem (by norm_num) h₁.1 hb
    · exact mem (by norm_num) h₂.1 hb
    · exact mem (by norm_num) h₃.1 hb
    · exact mem (by norm_num) h₄.1 hb
  · simp only [branchMass_append, branchMass_scale, h₁.2.1, h₂.2.1, h₃.2.1, h₄.2.1]
    norm_num
  · simp only [branchSum_append, branchSum_scale, ← h₁.2.2, ← h₂.2.2, ← h₃.2.2, ← h₄.2.2]
    exact hid ψ

/-! ### Bookkeeping -/

theorem euclideanSiteDistance_le (x y : Site L) : euclideanSiteDistance x y ≤ 2 * L := by
  unfold euclideanSiteDistance
  have h1 : ((x.1.val : ℕ) : ℝ) ≤ L := by exact_mod_cast x.1.isLt.le
  have h2 : ((y.1.val : ℕ) : ℝ) ≤ L := by exact_mod_cast y.1.isLt.le
  have h3 : ((x.2.val : ℕ) : ℝ) ≤ L := by exact_mod_cast x.2.isLt.le
  have h4 : ((y.2.val : ℕ) : ℝ) ≤ L := by exact_mod_cast y.2.isLt.le
  have h1' : (0 : ℝ) ≤ ((x.1.val : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2' : (0 : ℝ) ≤ ((y.1.val : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3' : (0 : ℝ) ≤ ((x.2.val : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4' : (0 : ℝ) ≤ ((y.2.val : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : ((x.1.val : ℝ) - y.1.val) ^ 2 + ((x.2.val : ℝ) - y.2.val) ^ 2 ≤ (2 * L) ^ 2 := by
    nlinarith
  calc _ ≤ Real.sqrt ((2 * L) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 2 * L := Real.sqrt_sq (by positivity)

theorem isBKTEnsemble_of_pinned {E : ChargeEnsemble L} (hE : IsPinnedChargeEnsemble E) :
    IsBKTEnsemble E := by
  refine ⟨hE.1, ?_⟩
  intro τ hτ υ hυ hne'
  apply Set.disjoint_left.mpr
  intro x hxτ hxυ
  have hxτ' : x ∈ chargeSupport τ := by
    simpa [chargeSupport, Function.mem_support] using hxτ
  have hxυ' : x ∈ chargeSupport υ := by
    simpa [chargeSupport, Function.mem_support] using hxυ
  exact (Finset.disjoint_left.mp (hE.2 τ hτ υ hυ hne') hxτ') hxυ'

theorem erase_erase_union {A F : Finset (ChargeDensity L)} {a c : ChargeDensity L}
    (haF : a ∉ F) (hcF : c ∉ F) :
    ((A ∪ F).erase a).erase c = (A.erase a).erase c ∪ F := by
  rw [Finset.erase_union_distrib, Finset.erase_union_distrib, Finset.erase_eq_of_notMem haF,
    Finset.erase_eq_of_notMem hcF]

theorem sdiff_union_union_eq {A F J : Finset (ChargeDensity L)} (hJA : J ⊆ A) :
    A \ J ∪ (F ∪ J) = A ∪ F := by
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  have := @hJA x
  tauto

/-! ### Pair steps are conflicts -/

variable {M α : ℝ}

/-- Every active at base `s` has `s < M d_Λ^α`: below scale `s` by the witness, and otherwise
because `d_Λ ≥ d ≥ s` with `d ≥ 1`. -/
theorem SelectionState.lt_mul_rpow (hM : 1 < M) (hα : 1 ≤ α) {s : ℝ} (hs : 0 < s)
    {A F : Finset (ChargeDensity L)} (h : SelectionState M α s A F) {ρ : ChargeDensity L}
    (hρ : ρ ∈ A) : s < M * boundaryAdjustedSize ρ ^ α := by
  by_cases hd : chargeEuclideanDiameter ρ < s
  · exact h.witness ρ hρ hd
  push Not at hd
  have hb := chargeEuclideanDiameter_le_boundaryAdjustedSize ρ
  rcases diam_eq_zero_or_one_le (chargeSupport ρ) with h0 | h1
  · exfalso
    change chargeEuclideanDiameter ρ = 0 at h0
    linarith
  · change 1 ≤ chargeEuclideanDiameter ρ at h1
    have hpow := le_rpow_self (h1.trans hb) hα
    nlinarith

/-- **Pair steps are conflicts.** Two actives at distance `≤ 2s` conflict at threshold `2M`:
`dist < 2M min(d_Λ)^α`. -/
theorem SelectionState.pairConflict (hM : 1 < M) (hα : 1 ≤ α) {s : ℝ} (hs : 0 < s)
    {A F : Finset (ChargeDensity L)} (h : SelectionState M α s A F) {a c : ChargeDensity L}
    (ha : a ∈ A) (hc : c ∈ A)
    (hD : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * s) :
    IsBoundaryPairConflict (2 * M) α a c := by
  left
  unfold boundaryPairThreshold
  rcases min_choice (boundaryAdjustedSize a) (boundaryAdjustedSize c) with hm | hm <;> rw [hm]
  · have := h.lt_mul_rpow hM hα hs ha
    linarith
  · have := h.lt_mul_rpow hM hα hs hc
    linarith

/-! ### The expansion -/

/-- One four-branch pair step at base `s`: the four branch states have one active fewer. -/
theorem pairStep (hM : 1 < M) (hα : 1 ≤ α) {s : ℝ} (hs : 0 < s) {A F : Finset (ChargeDensity L)}
    (h : SelectionState M α s A F) {a c : ChargeDensity L} (ha : a ∈ A) (hc : c ∈ A)
    (hne : a ≠ c) (hD : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * s)
    (K : ChargeDensity L → ℝ)
    (IH : ∀ A', A'.card < A.card → SelectionState M α s A' F →
      ∀ K', ∃ B, IsSelectionExpansion M α (A' ∪ F) K' B) :
    ∃ B, IsSelectionExpansion M α (A ∪ F) K B := by
  classical
  have haF : a ∉ F := fun h' => Finset.disjoint_left.mp h.disjoint ha h'
  have hcF : c ∉ F := fun h' => Finset.disjoint_left.mp h.disjoint hc h'
  have hcard1 : (A.erase c).card < A.card := Finset.card_erase_lt_of_mem hc
  have hcard2 : (A.erase a).card < A.card := Finset.card_erase_lt_of_mem ha
  have hcard3 : ∀ τ, (insert τ ((A.erase a).erase c)).card < A.card := by
    intro τ
    have hc' : c ∈ A.erase a := Finset.mem_erase.mpr ⟨Ne.symm hne, hc⟩
    have := Finset.card_insert_le τ ((A.erase a).erase c)
    have e1 := Finset.card_erase_of_mem hc'
    have e2 := Finset.card_erase_of_mem ha
    have hpos : 0 < (A.erase a).card := Finset.card_pos.mpr ⟨c, hc'⟩
    omega
  have hU : a ∈ A ∪ F := Finset.mem_union_left _ ha
  obtain ⟨B₁, h₁⟩ := IH _ hcard1 (h.erase c) (pairRewriteFirstCoefficient K a)
  obtain ⟨B₂, h₂⟩ := IH _ hcard2 (h.erase a) (pairRewriteSecondCoefficient K c)
  have hm₃ := h.merge hM hα hs ha hc hne hD (ε := -1) (Or.inr rfl)
  have hm₄ := h.merge hM hα hs ha hc hne hD (ε := 1) (Or.inl rfl)
  rw [neg_one_smul, ← sub_eq_add_neg] at hm₃
  rw [one_smul] at hm₄
  obtain ⟨B₃, h₃⟩ := IH _ (hcard3 _) hm₃ (pairRewriteDifferenceCoefficient K a c)
  obtain ⟨B₄, h₄⟩ := IH _ (hcard3 _) hm₄ (pairRewriteSumCoefficient K a c)
  refine ⟨_, IsSelectionExpansion.combine h₁ h₂ h₃ h₄ fun ψ => ?_⟩
  have hid := chargeFactorProduct_pairBranches_identity (A ∪ F) (isBKTEnsemble_of_pinned h.pinned)
    K ψ a c hU (Finset.mem_union_left _ hc) hne
  simp only at hid
  rw [hid, erase_erase_union haF hcF]
  have e₁ : insert a ((A.erase a).erase c ∪ F) = A.erase c ∪ F := by
    rw [← Finset.insert_union, Finset.erase_right_comm,
      Finset.insert_erase (Finset.mem_erase.mpr ⟨hne, ha⟩)]
  have e₂ : insert c ((A.erase a).erase c ∪ F) = A.erase a ∪ F := by
    rw [← Finset.insert_union, Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hne, hc⟩)]
  rw [e₁, e₂, ← Finset.insert_union, ← Finset.insert_union]

/-- Every selection state at base `2^j / 2` has a selection expansion of its ensemble. -/
theorem exists_selectionExpansion (hM : 1 < M) (hα : 1 ≤ α) :
    ∀ (n : ℕ) (k : ℕ) (j : ℕ) (A F : Finset (ChargeDensity L)), A.card = n → 2 * L - j = k →
      SelectionState M α ((2 : ℝ) ^ j / 2) A F →
      ∀ K, ∃ B, IsSelectionExpansion M α (A ∪ F) K B := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro j A F hn hk h K
  have hs : (0 : ℝ) < (2 : ℝ) ^ j / 2 := by positivity
  by_cases hA : A = ∅
  · -- terminal: a single branch
    subst hA
    refine ⟨[(1, ∅ ∪ F, K)], ?_, ?_, ?_⟩
    · intro b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact ⟨one_pos, by simpa using h.geometry⟩
    · simp [branchMass]
    · intro ψ
      simp [branchSum]
  by_cases hpair : ∃ a ∈ A, ∃ c ∈ A, a ≠ c ∧
      euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * ((2 : ℝ) ^ j / 2)
  · -- a four-branch pair step at the current scale
    obtain ⟨a, ha, c, hc, hne, hD⟩ := hpair
    exact pairStep hM hα hs h ha hc hne hD K fun A' hA' h' K' =>
      ihn _ (hn ▸ hA') (2 * L - j) j A' F rfl rfl h' K'
  · -- freezing stage: double the scale
    push Not at hpair
    have hfar : ∀ ρ ∈ A, ∀ σ ∈ A, ρ ≠ σ →
        2 * ((2 : ℝ) ^ j / 2) < euclideanSetDistance (chargeSupport ρ) (chargeSupport σ) :=
      fun ρ hρ σ hσ hne => hpair ρ hρ σ hσ hne
    obtain ⟨J, hJ⟩ := exists_maximalFreezeSet M α A
    have hM0 : (0 : ℝ) ≤ M := by linarith
    have hα0 : (0 : ℝ) ≤ α := by linarith
    have h' := h.freeze hM0 hα0 hs.le hfar hJ
    have hscale : 2 * ((2 : ℝ) ^ j / 2) = (2 : ℝ) ^ (j + 1) / 2 := by ring
    rw [hscale] at h'
    have hU := sdiff_union_union_eq (F := F) hJ.1.1
    rw [← hU]
    by_cases hJne : J.Nonempty
    · have hlt : (A \ J).card < A.card :=
        Finset.card_lt_card (Finset.sdiff_ssubset hJ.1.1 hJne)
      exact ihn _ (hn ▸ hlt) _ (j + 1) _ _ rfl rfl h' K
    ·
      have hJe : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJne
      obtain ⟨ρ, hρ⟩ := Finset.nonempty_iff_ne_empty.mpr hA
      have hσ : ∃ σ ∈ A, σ ≠ ρ := by
        by_contra hno
        push Not at hno
        refine hJ.2 ρ (by simpa [hJe] using hρ) ?_
        rw [hJe]
        refine ⟨by simpa using hρ, fun ρ' hρ' σ hσ => ?_, fun x hx y hy hxy => ?_⟩
        · obtain ⟨hσA, hσn⟩ := Finset.mem_sdiff.mp hσ
          exact absurd (hno σ hσA) (by simpa using hσn)
        · simp only [insert_empty_eq, Finset.mem_singleton] at hx hy
          exact absurd (hx.trans hy.symm) hxy
      obtain ⟨σ, hσA, hσρ⟩ := hσ
      have hρne := chargeSupport_nonempty_of_ne_zero ρ
        (h.ne_zero (Finset.mem_union_left _ hρ))
      have hσne := chargeSupport_nonempty_of_ne_zero σ
        (h.ne_zero (Finset.mem_union_left _ hσA))
      obtain ⟨x, hx⟩ := hρne
      obtain ⟨y, hy⟩ := hσne
      have hbox : (2 : ℝ) ^ j < 2 * L := by
        have := hfar ρ hρ σ hσA (Ne.symm hσρ)
        have := (setDist_le_siteDist hx hy).trans (euclideanSiteDistance_le x y)
        linarith
      have hjL : j < 2 * L := by
        have h2 : 2 ^ j < 2 * L := by exact_mod_cast hbox
        exact (Nat.lt_two_pow_self).trans h2
      rw [hJe] at h' ⊢
      exact ihk (2 * L - (j + 1)) (by omega) (j + 1) _ _ (by rw [Finset.sdiff_empty]; exact hn)
        rfl (by simpa using h') K

/-- **The selection expansion.** For `M > 1`, `α ≥ 1`, every pinned ensemble `E` of single-site
densities and every coefficient function `K`, the charge-factor product
`∏_{ρ ∈ E} (1 + K(ρ) cos⟨ψ, ρ⟩)` is a finite convex combination, uniformly in `ψ`, of
charge-factor products over terminal ensembles, each pinned, boundary-separated and
boundary-isolated (`AppendixDChargeGeometry M α`). The branch coefficients are FS81's (2.13)
updates `3K₁`, `3K₂`, `3K₁K₂`. -/
theorem exists_selectionExpansion_of_singleSites (hM : 1 < M) (hα : 1 ≤ α)
    {E : ChargeEnsemble L} (hE : IsPinnedChargeEnsemble E)
    (hsingle : ∀ ρ ∈ E, (chargeSupport ρ).card = 1) (K : ChargeDensity L → ℝ) :
    ∃ B, IsSelectionExpansion M α E K B := by
  have h := SelectionState.initial (M := M) (α := α) hM hα hE hsingle
  have h0 : (1 / 2 : ℝ) = (2 : ℝ) ^ 0 / 2 := by norm_num
  rw [h0] at h
  simpa using exists_selectionExpansion hM hα _ _ 0 E ∅ rfl rfl h K

end FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

end
