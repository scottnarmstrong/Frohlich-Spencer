/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGState

/-!
Maximality gives the strong witness `2s < M d_Λ(ρ)^α` for every remaining active `ρ`
(`two_mul_lt_of_maximal`): this is the (I5) bound at the new base `2s`, and it is what bounds the
crossing distance when such a `ρ` is later merged as a whole operand.

The start (`SelectionState.initial`) is any pinned ensemble of single-site densities at `s = 1/2`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

open FroehlichSpencer.BKT

variable {L : ℕ}


def IsFreezeSet (M α : ℝ) (A J : Finset (ChargeDensity L)) : Prop :=
  J ⊆ A ∧
    (∀ ρ ∈ J, ∀ σ ∈ A \ J,
      M * boundaryAdjustedSize ρ ^ α ≤ euclideanSetDistance (chargeSupport ρ) (chargeSupport σ)) ∧
    IsBoundarySeparated M α J


def IsMaximalFreezeSet (M α : ℝ) (A J : Finset (ChargeDensity L)) : Prop :=
  IsFreezeSet M α A J ∧ ∀ ρ ∈ A \ J, ¬ IsFreezeSet M α A (insert ρ J)

theorem isFreezeSet_empty (M α : ℝ) (A : Finset (ChargeDensity L)) : IsFreezeSet M α A ∅ :=
  ⟨Finset.empty_subset _, by simp, by simp [IsBoundarySeparated]⟩


theorem exists_maximalFreezeSet (M α : ℝ) (A : Finset (ChargeDensity L)) :
    ∃ J, IsMaximalFreezeSet M α A J := by
  classical
  let P := A.powerset.filter (IsFreezeSet M α A)
  have hP : P.Nonempty := ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.empty_mem_powerset _, isFreezeSet_empty M α A⟩⟩
  obtain ⟨J, hJP, hJmax⟩ := Finset.exists_max_image P Finset.card hP
  refine ⟨J, (Finset.mem_filter.mp hJP).2, fun ρ hρ hins => ?_⟩
  have hρJ := (Finset.mem_sdiff.mp hρ).2
  have hmem : insert ρ J ∈ P :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hins.1, hins⟩
  have := hJmax _ hmem
  rw [Finset.card_insert_of_notMem hρJ] at this
  omega


theorem IsFreezeSet.insert {M α : ℝ} (hM : 0 ≤ M) (hα : 0 ≤ α) {A J : Finset (ChargeDensity L)}
    (hJ : IsFreezeSet M α A J) {ρ : ChargeDensity L} (hρ : ρ ∈ A) (hρJ : ρ ∉ J)
    (hδ : ∀ σ ∈ A \ insert ρ J,
      M * boundaryAdjustedSize ρ ^ α ≤ euclideanSetDistance (chargeSupport ρ) (chargeSupport σ)) :
    IsFreezeSet M α A (insert ρ J) := by
  refine ⟨Finset.insert_subset hρ hJ.1, fun ρ' hρ' σ hσ => ?_, fun x hx y hy hxy => ?_⟩
  · rcases Finset.mem_insert.mp hρ' with rfl | hρ'
    · exact hδ σ hσ
    · obtain ⟨hσA, hσn⟩ := Finset.mem_sdiff.mp hσ
      exact hJ.2.1 ρ' hρ' σ (Finset.mem_sdiff.mpr ⟨hσA, fun h => hσn (Finset.mem_insert_of_mem h)⟩)
  · have hρAJ : ρ ∈ A \ J := Finset.mem_sdiff.mpr ⟨hρ, hρJ⟩
    rcases Finset.mem_insert.mp hx with hxρ | hxJ <;> rcases Finset.mem_insert.mp hy with hyρ | hyJ
    · exact absurd (hxρ.trans hyρ.symm) hxy
    · rw [hxρ, setDist_comm]
      exact (mul_min_rpow_le_right hM hα _ _).trans (hJ.2.1 y hyJ _ hρAJ)
    · rw [hyρ]
      exact (mul_min_rpow_le_left hM hα _ _).trans (hJ.2.1 x hxJ _ hρAJ)
    · exact hJ.2.2 x hxJ y hyJ hxy


theorem two_mul_lt_of_maximal {M α s : ℝ} (hM : 0 ≤ M) (hα : 0 ≤ α)
    {A J : Finset (ChargeDensity L)} (hJ : IsMaximalFreezeSet M α A J)
    (hfar : ∀ ρ ∈ A, ∀ σ ∈ A, ρ ≠ σ →
      2 * s < euclideanSetDistance (chargeSupport ρ) (chargeSupport σ))
    {ρ : ChargeDensity L} (hρ : ρ ∈ A \ J) : 2 * s < M * boundaryAdjustedSize ρ ^ α := by
  by_contra hle
  push Not at hle
  obtain ⟨hρA, hρJ⟩ := Finset.mem_sdiff.mp hρ
  refine hJ.2 ρ hρ (hJ.1.insert hM hα hρA hρJ fun σ hσ => ?_)
  obtain ⟨hσA, hσn⟩ := Finset.mem_sdiff.mp hσ
  have hσρ : ρ ≠ σ := fun h => hσn (h ▸ Finset.mem_insert_self ρ J)
  exact hle.trans (hfar ρ hρA σ hσA hσρ).le

namespace SelectionState

variable {M α s : ℝ} {A F : Finset (ChargeDensity L)}


theorem freeze (hM : 0 ≤ M) (hα : 0 ≤ α) (hs : 0 ≤ s) (h : SelectionState M α s A F)
    (hfar : ∀ ρ ∈ A, ∀ σ ∈ A, ρ ≠ σ →
      2 * s < euclideanSetDistance (chargeSupport ρ) (chargeSupport σ))
    {J : Finset (ChargeDensity L)} (hJ : IsMaximalFreezeSet M α A J) :
    SelectionState M α (2 * s) (A \ J) (F ∪ J) := by
  have hJA := hJ.1.1
  have hU : A \ J ∪ (F ∪ J) = A ∪ F := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    have := @hJA x
    tauto
  have hAJ : ∀ {σ}, σ ∈ A \ J → σ ∈ A := fun hσ => (Finset.mem_sdiff.mp hσ).1
  refine
    { pinned := hU ▸ h.pinned
      disjoint := Finset.disjoint_union_right.mpr
        ⟨h.disjoint.mono_left Finset.sdiff_subset, Finset.sdiff_disjoint⟩
      isolated := hU ▸ h.isolated
      separated := fun ρ hρ σ hσ hne => hfar ρ (hAJ hρ) σ (hAJ hσ) hne
      connected := fun ρ hρ => (h.connected ρ (hAJ hρ)).mono (by linarith)
      witness := fun ρ hρ _ => two_mul_lt_of_maximal hM hα hJ hfar hρ
      sourceActive := fun φ hφ σ hσ => ?_
      frozen := fun x hx y hy hxy => ?_ }
  · rcases Finset.mem_union.mp hφ with hφ | hφ
    · exact h.sourceActive φ hφ σ (hAJ hσ)
    · exact hJ.1.2.1 φ hφ σ hσ
  · rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
    · exact h.frozen x hx y hy hxy
    · exact (mul_min_rpow_le_left hM hα _ _).trans (h.sourceActive x hx y (hJA hy))
    · rw [setDist_comm]
      exact (mul_min_rpow_le_right hM hα _ _).trans (h.sourceActive y hy x (hJA hx))
    · exact hJ.1.2.2 x hx y hy hxy

/-! ### The single-site start -/

theorem totalCharge_of_support_singleton {ρ : ChargeDensity L} {x : Site L}
    (h : chargeSupport ρ = {x}) : totalCharge ρ = ρ x := by
  unfold totalCharge
  refine Finset.sum_eq_single x (fun y _ hy => ?_) (fun hx => absurd (Finset.mem_univ x) hx)
  have : y ∉ chargeSupport ρ := by rw [h]; simpa using hy
  simpa [chargeSupport] using this

theorem totalCharge_ne_zero_of_support_singleton {ρ : ChargeDensity L} {x : Site L}
    (h : chargeSupport ρ = {x}) : totalCharge ρ ≠ 0 := by
  rw [totalCharge_of_support_singleton h]
  have : x ∈ chargeSupport ρ := by rw [h]; exact Finset.mem_singleton_self x
  simpa [chargeSupport] using this

/--
**Initial state.** A pinned ensemble of single-site densities is a selection state at base
`1/2` with nothing .
-/
theorem initial (hM : 1 < M) (hα : 1 ≤ α) (hA : IsPinnedChargeEnsemble A)
    (hsingle : ∀ ρ ∈ A, (chargeSupport ρ).card = 1) : SelectionState M α (1 / 2) A ∅ := by
  have hpt : ∀ ρ ∈ A, ∃ x, chargeSupport ρ = {x} := fun ρ hρ => Finset.card_eq_one.mp (hsingle ρ hρ)
  refine
    { pinned := by simpa using hA
      disjoint := Finset.disjoint_empty_right _
      isolated := fun ρ hρ => ?_
      separated := fun ρ hρ σ hσ hne => ?_
      connected := fun ρ hρ => ?_
      witness := fun ρ hρ _ => ?_
      sourceActive := fun φ hφ => absurd hφ (Finset.notMem_empty φ)
      frozen := by simp [IsBoundarySeparated] }
  · rw [Finset.union_empty] at hρ
    obtain ⟨x, hx⟩ := hpt ρ hρ
    intro ρ₁ hρ₁ _
    have hne := chargeSupport_nonempty_of_ne_zero ρ₁ hρ₁.1
    have hsub : chargeSupport ρ₁ ⊆ {x} := hx ▸ hρ₁.2.1
    have hx₁ : chargeSupport ρ₁ = {x} :=
      (Finset.subset_singleton_iff.mp hsub).resolve_left hne.ne_empty
    rw [chargeSupport_sub_constituent hρ₁, hx, hx₁, Finset.sdiff_self, setDist_empty_right]
    refine ⟨totalCharge_ne_zero_of_support_singleton hx₁, ?_⟩
    have := chargeBoundaryDistance_ge_one_of_ne_zero ρ₁ hρ₁.1
    have : 0 ≤ chargeBoundaryDistance ρ₁ ^ α := Real.rpow_nonneg (by linarith) α
    nlinarith
  · obtain ⟨x, hx⟩ := hpt ρ hρ
    obtain ⟨y, hy⟩ := hpt σ hσ
    have hd := hA.2 ρ hρ σ hσ hne
    rw [hx, hy] at hd ⊢
    have hxy : x ≠ y := fun h => by
      rw [h] at hd
      exact Finset.disjoint_left.mp hd (Finset.mem_singleton_self y) (Finset.mem_singleton_self y)
    have := le_setDist (Finset.singleton_nonempty x) (Finset.singleton_nonempty y)
      (c := 1) fun x' hx' y' hy' => by
        rw [Finset.mem_singleton] at hx' hy'
        subst hx' hy'
        exact one_le_siteDist hxy
    linarith
  · obtain ⟨x, hx⟩ := hpt ρ hρ
    intro S hS hSne hT
    rw [hx] at hS hT
    have hSx : S = {x} := (Finset.subset_singleton_iff.mp hS).resolve_left hSne.ne_empty
    rw [hSx, Finset.sdiff_self] at hT
    exact absurd hT Finset.not_nonempty_empty
  · obtain ⟨x, hx⟩ := hpt ρ hρ
    have hq := totalCharge_ne_zero_of_support_singleton hx
    have hρ0 : ρ ≠ 0 := hA.1 ρ hρ
    rw [boundaryAdjustedSize_of_charged ρ hq]
    have h1 : 1 ≤ max (chargeBoundaryDistance ρ) (chargeEuclideanDiameter ρ) :=
      (chargeBoundaryDistance_ge_one_of_ne_zero ρ hρ0).trans (le_max_left _ _)
    have h2 := Real.one_le_rpow h1 (by linarith : (0 : ℝ) ≤ α)
    nlinarith

end SelectionState

end FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

end
