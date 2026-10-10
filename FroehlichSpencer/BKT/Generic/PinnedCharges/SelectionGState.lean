/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGMerge

/-!
The selection runs at base scales `s = 1/2, 1, 2, …` on a family `A` of active densities and a
family `F` of  ones.

At base `s` it applies FS81's (2.13) four-branch rewrite to active pairs
at distance `≤ 2s` (keep one / merge `a ± c`); when the actives are pairwise farther than `2s` it
freezes a maximal subfamily `J` and doubles the scale.

`SelectionState M α s A F` records the invariants (I1)–(I6).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

open FroehlichSpencer.BKT

variable {L : ℕ}

/--
The selection invariants at base scale `s`:
(I1) `A ∪ F` pinned, `A ∩ F = ∅`; (I2) isolation; (I3) actives `> s` apart; (I4) actives
`2s`-connected; (I5) the scale witness; (I6)  separation.
-/
structure SelectionState (M α s : ℝ) (A F : Finset (ChargeDensity L)) : Prop where
  pinned : IsPinnedChargeEnsemble (A ∪ F)
  disjoint : Disjoint A F
  isolated : ∀ ρ ∈ A ∪ F, IsIsolated M α ρ
  separated : ∀ ρ ∈ A, ∀ σ ∈ A, ρ ≠ σ →
    s < euclideanSetDistance (chargeSupport ρ) (chargeSupport σ)
  connected : ∀ ρ ∈ A, IsScaleConnected (2 * s) ρ
  witness : ∀ ρ ∈ A, HasScaleWitness M α s ρ
  sourceActive : ∀ φ ∈ F, ∀ σ ∈ A,
    M * boundaryAdjustedSize φ ^ α ≤ euclideanSetDistance (chargeSupport φ) (chargeSupport σ)
  frozen : IsBoundarySeparated M α F

theorem boundaryAdjustedSize_nonneg (ρ : ChargeDensity L) : 0 ≤ boundaryAdjustedSize ρ :=
  (diam_nonneg _).trans (chargeEuclideanDiameter_le_boundaryAdjustedSize ρ)

/-- `M min(x, y)^α ≤ M y^α` for the sizes `x, y ≥ 0`. -/
theorem mul_min_rpow_le_right {M α : ℝ} (hM : 0 ≤ M) (hα : 0 ≤ α) (ρ σ : ChargeDensity L) :
    M * min (boundaryAdjustedSize ρ) (boundaryAdjustedSize σ) ^ α ≤
      M * boundaryAdjustedSize σ ^ α :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
    (le_min (boundaryAdjustedSize_nonneg ρ) (boundaryAdjustedSize_nonneg σ)) (min_le_right _ _)
    hα) hM

theorem mul_min_rpow_le_left {M α : ℝ} (hM : 0 ≤ M) (hα : 0 ≤ α) (ρ σ : ChargeDensity L) :
    M * min (boundaryAdjustedSize ρ) (boundaryAdjustedSize σ) ^ α ≤
      M * boundaryAdjustedSize ρ ^ α := by
  rw [min_comm]
  exact mul_min_rpow_le_right hM hα σ ρ

namespace SelectionState

variable {M α s : ℝ} {A F : Finset (ChargeDensity L)}

theorem ne_zero (h : SelectionState M α s A F) {ρ : ChargeDensity L} (hρ : ρ ∈ A ∪ F) : ρ ≠ 0 :=
  h.pinned.1 ρ hρ

theorem disjoint_support (h : SelectionState M α s A F) {ρ σ : ChargeDensity L}
    (hρ : ρ ∈ A ∪ F) (hσ : σ ∈ A ∪ F) (hne : ρ ≠ σ) :
    Disjoint (chargeSupport ρ) (chargeSupport σ) :=
  h.pinned.2 ρ hρ σ hσ hne

/--
**Terminal ensembles.** With no actives left, the family has the full Appendix D
geometry (pinned, boundary-separated, boundary-isolated).
-/
theorem geometry (h : SelectionState M α s ∅ F) : AppendixDChargeGeometry M α F where
  ensemble := by simpa using h.pinned
  separated := h.frozen
  isolated := fun ρ hρ => h.isolated ρ (by simpa using hρ)

/-! ### Elimination (branches "keep one" of (2.13)) -/

theorem erase (h : SelectionState M α s A F) (c : ChargeDensity L) :
    SelectionState M α s (A.erase c) F := by
  have hsub : A.erase c ∪ F ⊆ A ∪ F := Finset.union_subset_union (Finset.erase_subset _ _) subset_rfl
  have hA : ∀ {ρ}, ρ ∈ A.erase c → ρ ∈ A := fun hρ => Finset.mem_of_mem_erase hρ
  exact
    { pinned := ⟨fun ρ hρ => h.pinned.1 ρ (hsub hρ),
        fun ρ hρ σ hσ hne => h.pinned.2 ρ (hsub hρ) σ (hsub hσ) hne⟩
      disjoint := h.disjoint.mono_left (Finset.erase_subset _ _)
      isolated := fun ρ hρ => h.isolated ρ (hsub hρ)
      separated := fun ρ hρ σ hσ hne => h.separated ρ (hA hρ) σ (hA hσ) hne
      connected := fun ρ hρ => h.connected ρ (hA hρ)
      witness := fun ρ hρ => h.witness ρ (hA hρ)
      sourceActive := fun φ hφ σ hσ => h.sourceActive φ hφ σ (hA hσ)
      frozen := h.frozen }

/-! ### Merging (branches `a ± c` of (2.13)) -/

theorem dist_merge_ge {a c σ : ChargeDensity L} {r : ℝ} (ha : (chargeSupport a).Nonempty)
    (hσ : (chargeSupport σ).Nonempty)
    (hac : r ≤ euclideanSetDistance (chargeSupport a) (chargeSupport σ))
    (hcc : r ≤ euclideanSetDistance (chargeSupport c) (chargeSupport σ)) :
    r ≤ euclideanSetDistance (chargeSupport a ∪ chargeSupport c) (chargeSupport σ) :=
  (le_min hac hcc).trans (min_le_setDist_union ha hσ)

/-- **Merge transition.** Replacing active `a, c` at distance `≤ 2s` by `a + ε c` (`ε = ±1`)
preserves the invariants. -/
theorem merge (hM : 1 < M) (hα : 1 ≤ α) (hs : 0 < s) (h : SelectionState M α s A F)
    {a c : ChargeDensity L} (ha : a ∈ A) (hc : c ∈ A) (hne : a ≠ c)
    (hD : euclideanSetDistance (chargeSupport a) (chargeSupport c) ≤ 2 * s)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    SelectionState M α s (insert (a + ε • c) ((A.erase a).erase c)) F := by
  set τ := a + ε • c with hτdef
  have haU : a ∈ A ∪ F := Finset.mem_union_left _ ha
  have hcU : c ∈ A ∪ F := Finset.mem_union_left _ hc
  have hane := chargeSupport_nonempty_of_ne_zero a (h.ne_zero haU)
  have hcne := chargeSupport_nonempty_of_ne_zero c (h.ne_zero hcU)
  have hdisj := h.disjoint_support haU hcU hne
  obtain ⟨hiso, hcon, hwit, hsupp, -⟩ :=
    merge_signed hM hα hs hε (h.ne_zero haU) (h.ne_zero hcU) hdisj (h.separated a ha c hc hne) hD
      (h.isolated a haU) (h.isolated c hcU) (h.connected a ha) (h.connected c hc) (h.witness a ha)
      (h.witness c hc)
  rw [← hτdef] at hiso hcon hwit hsupp
  have hτne : τ ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := hane
    have hxτ : x ∈ chargeSupport τ := hsupp ▸ Finset.mem_union_left _ hx
    rw [h0] at hxτ
    simp [chargeSupport] at hxτ
  -- the surviving old densities
  have old : ∀ {σ}, σ ∈ (A.erase a).erase c → σ ∈ A ∧ σ ≠ a ∧ σ ≠ c := by
    intro σ hσ
    obtain ⟨hσc, hσ'⟩ := Finset.mem_erase.mp hσ
    obtain ⟨hσa, hσA⟩ := Finset.mem_erase.mp hσ'
    exact ⟨hσA, hσa, hσc⟩
  have hmem : ∀ {ρ}, ρ ∈ insert τ ((A.erase a).erase c) ∪ F →
      ρ = τ ∨ (ρ ∈ A ∪ F ∧ ρ ≠ a ∧ ρ ≠ c) := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with hρ | hρF
    · rcases Finset.mem_insert.mp hρ with rfl | hρ
      · exact Or.inl rfl
      · obtain ⟨h1, h2, h3⟩ := old hρ
        exact Or.inr ⟨Finset.mem_union_left _ h1, h2, h3⟩
    · refine Or.inr ⟨Finset.mem_union_right _ hρF, ?_, ?_⟩
      · rintro rfl
        exact Finset.disjoint_left.mp h.disjoint ha hρF
      · rintro rfl
        exact Finset.disjoint_left.mp h.disjoint hc hρF
  -- old densities are disjoint from the merged support
  have hdisjτ : ∀ {σ}, σ ∈ A ∪ F → σ ≠ a → σ ≠ c →
      Disjoint (chargeSupport τ) (chargeSupport σ) := by
    intro σ hσ hσa hσc
    rw [hsupp]
    exact Finset.disjoint_union_left.mpr
      ⟨h.disjoint_support haU hσ (Ne.symm hσa), h.disjoint_support hcU hσ (Ne.symm hσc)⟩
  have hτF : τ ∉ F := by
    intro hτF
    have hτa : τ ≠ a := by
      rintro hτa
      exact Finset.disjoint_left.mp h.disjoint ha (hτa ▸ hτF)
    have hτc : τ ≠ c := by
      rintro hτc
      exact Finset.disjoint_left.mp h.disjoint hc (hτc ▸ hτF)
    have hd := hdisjτ (Finset.mem_union_right _ hτF) hτa hτc
    obtain ⟨x, hx⟩ := hane
    have hxτ : x ∈ chargeSupport τ := hsupp ▸ Finset.mem_union_left _ hx
    exact Finset.disjoint_left.mp hd hxτ hxτ
  refine
    { pinned := ⟨fun ρ hρ => ?_, fun ρ hρ σ hσ hρσ => ?_⟩
      disjoint := ?_
      isolated := fun ρ hρ => ?_
      separated := fun ρ hρ σ hσ hρσ => ?_
      connected := fun ρ hρ => ?_
      witness := fun ρ hρ => ?_
      sourceActive := fun φ hφ σ hσ => ?_
      frozen := h.frozen }
  · rcases hmem hρ with rfl | ⟨hρ, -, -⟩
    · exact hτne
    · exact h.ne_zero hρ
  · rcases hmem hρ with rfl | ⟨hρU, hρa, hρc⟩ <;> rcases hmem hσ with rfl | ⟨hσU, hσa, hσc⟩
    · exact absurd rfl hρσ
    · exact hdisjτ hσU hσa hσc
    · exact (hdisjτ hρU hρa hρc).symm
    · exact h.disjoint_support hρU hσU hρσ
  · rw [Finset.disjoint_insert_left]
    exact ⟨hτF, h.disjoint.mono_left ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))⟩
  · rcases hmem hρ with rfl | ⟨hρU, -, -⟩
    · exact hiso
    · exact h.isolated ρ hρU
  · have hdist : ∀ {σ}, σ ∈ (A.erase a).erase c →
        s < euclideanSetDistance (chargeSupport τ) (chargeSupport σ) := by
      intro σ hσ
      obtain ⟨hσA, hσa, hσc⟩ := old hσ
      have hσne := chargeSupport_nonempty_of_ne_zero σ (h.ne_zero (Finset.mem_union_left _ hσA))
      rw [hsupp]
      have h1 := h.separated a ha σ hσA (Ne.symm hσa)
      have h2 := h.separated c hc σ hσA (Ne.symm hσc)
      exact (lt_min h1 h2).trans_le (min_le_setDist_union hane hσne)
    rcases Finset.mem_insert.mp hρ with rfl | hρ' <;> rcases Finset.mem_insert.mp hσ with rfl | hσ'
    · exact absurd rfl hρσ
    · exact hdist hσ'
    · rw [setDist_comm]
      exact hdist hρ'
    · exact h.separated ρ (old hρ').1 σ (old hσ').1 hρσ
  · rcases Finset.mem_insert.mp hρ with rfl | hρ'
    · exact hcon
    · exact h.connected ρ (old hρ').1
  · rcases Finset.mem_insert.mp hρ with rfl | hρ'
    · exact hwit
    · exact h.witness ρ (old hρ').1
  · rcases Finset.mem_insert.mp hσ with rfl | hσ'
    · have hφne := chargeSupport_nonempty_of_ne_zero φ (h.ne_zero (Finset.mem_union_right _ hφ))
      rw [setDist_comm, hsupp]
      have h1 := h.sourceActive φ hφ a ha
      have h2 := h.sourceActive φ hφ c hc
      rw [setDist_comm] at h1 h2
      exact dist_merge_ge hane hφne h1 h2
    · exact h.sourceActive φ hφ σ (old hσ').1

end SelectionState

end FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

end
