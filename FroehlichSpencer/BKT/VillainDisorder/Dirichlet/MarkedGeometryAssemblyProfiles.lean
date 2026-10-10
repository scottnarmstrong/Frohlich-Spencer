/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryProfileEnergy
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileGInterface
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileGSplit
import Mathlib.Tactic

/-!
The P4.7 profile family of `terminalProfilesA` uses the comb-terminal history only to produce the
profile contexts.

This file:
* builds `markedProfilesG F : TerminalProfilesG L α 6400 8 F` for every such family `F`, in
  particular for the marked extension `rem(C) ∪ {p}`;
* proves the clauses of `routineWave` (orthogonality, cross-density gradient disjointness, half
  mass, edge counts) for a general pinned separated family, as in
  `pinnedTerminalWavesW_of_profilesW`;
* proves that a profile piece is constant on the face support of every other density of its family
  (`ProfileContext.profilePiece_eq_of_mem_other`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG
open FroehlichSpencer.BKT.Rotator

variable {L : ℕ}

/-! ### The profile family of a pinned separated family -/

/-- **Part (A) on a pinned separated family**: `terminalProfilesA` with the contexts of
`rootedMarkedProfileContext_of_profileIndex` (no comb history). -/
def markedProfilesG {F : Finset (ChargeDensity L)} (hFzero : ∀ σ ∈ F, σ ≠ 0)
    (hFsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    (hL : 1 < L) (α : ℝ) (hα : 0 ≤ α) :
    TerminalProfilesG L α 6400 8 F where
  ι := fun ϱ => profileIndex ϱ
  fin := fun _ => inferInstance
  scale := fun _ t => t.1.1 + 3
  piece := fun ϱ t => profileFamilyPiece F ϱ t.1
  charge := fun ϱ t => (totalCharge (chargeRestriction (siteRestrict ϱ) t.1.2) : ℝ)
  one_le_scale := fun _ _ _ => by omega
  pairing := by
    intro ϱ hϱ t
    have hc := rootedMarkedProfileContext_of_profileIndex hFzero hFsep hϱ t.1 t.2
    have hp := hc.pairing_profilePiece
    rw [(neutralize_siteRestrict_of_mem hϱ).2] at hp
    exact hp
  charge_ge_one := by
    intro ϱ hϱ t
    have hc := rootedMarkedProfileContext_of_profileIndex hFzero hFsep hϱ t.1 t.2
    have : (1 : ℤ) ≤ |totalCharge (chargeRestriction (siteRestrict ϱ) t.1.2)| :=
      Int.one_le_abs hc.square.charged
    rw [← Int.cast_abs]
    exact_mod_cast this
  energy_le := by
    intro ϱ hϱ t
    have hc := rootedMarkedProfileContext_of_profileIndex hFzero hFsep hϱ t.1 t.2
    have he := hc.energy_profilePiece_le hL
    have h1 : (1 : ℝ) ≤ |(totalCharge (chargeRestriction (siteRestrict ϱ) t.1.2) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hc.square.charged
    have h2 : (1 : ℝ) ≤ (totalCharge (chargeRestriction (siteRestrict ϱ) t.1.2) : ℝ) ^ 2 := by
      rw [← sq_abs]; nlinarith
    show (squareZero L).energy (profileFamilyPiece F ϱ t.1) ≤ 6400 * _
    unfold profileFamilyPiece
    nlinarith
  grad_le := by
    intro ϱ hϱ t e
    have hc := rootedMarkedProfileContext_of_profileIndex hFzero hFsep hϱ t.1 t.2
    exact (hc.abs_grad_profilePiece_le hL e).trans (inv_two_pow_le α hα t.1.1)
  edge_count := by
    intro ϱ hϱ t
    exact (rootedMarkedProfileContext_of_profileIndex hFzero hFsep hϱ t.1 t.2).card_grad_profilePiece_ne_zero_le hL
  grad_disjoint := by
    intro ϱ hϱ t t' hne e
    have hc := rootedMarkedProfileContext_of_profileIndex hFzero hFsep hϱ t.1 t.2
    have hc' := rootedMarkedProfileContext_of_profileIndex hFzero hFsep hϱ t'.1 t'.2
    have hr : t.1.1 % 3 = t'.1.1 % 3 := by
      have h1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp t.2).1).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_sigma.mp t'.2).1).2
      rw [h1, h2]
    rcases lt_trichotomy t.1.1 t'.1.1 with hlt | heq | hgt
    · exact (hc'.grad_disjoint_same hc hL (Or.inr (by omega)) e).symm
    · refine hc.grad_disjoint_same hc' hL (Or.inl ⟨heq, fun hss => hne ?_⟩) e
      apply Subtype.ext
      exact Sigma.ext heq (heq_of_eq hss)
    · exact hc.grad_disjoint_same hc' hL (Or.inr (by omega)) e
  supp := by
    intro ϱ hϱ t
    have hc := rootedMarkedProfileContext_of_profileIndex hFzero hFsep hϱ t.1 t.2
    have hs := hc.support_profilePiece_subset hL
    rw [(neutralize_siteRestrict_of_mem hϱ).2] at hs
    exact hs
  count := by
    intro ϱ _
    rw [zero_mul]
    exact Nat.cast_nonneg _
  local_ := by
    intro ϱ hϱ t e he
    have hc := rootedMarkedProfileContext_of_profileIndex hFzero hFsep hϱ t.1 t.2
    have hm := hc.grad_profilePiece_mem_routineS hL he
    rw [(neutralize_siteRestrict_of_mem hϱ).2] at hm
    exact hm
  avoid := by
    intro ϱ hϱ t σ hσ x hx e hinc
    exact (rootedMarkedProfileContext_of_profileIndex hFzero hFsep hϱ t.1 t.2).grad_eq_zero_of_incident
      hL hσ hx hinc
  orth := by
    intro ϱ hϱ t ϱ' hϱ' hne
    have hc := rootedMarkedProfileContext_of_profileIndex hFzero hFsep hϱ t.1 t.2
    obtain ⟨hσ, hσeq⟩ := neutralize_siteRestrict_of_mem hϱ'
    have hσne : siteRestrict ϱ' ≠ siteRestrict ϱ := by
      intro h0
      apply hne
      rw [← hσeq, h0, (neutralize_siteRestrict_of_mem hϱ).2]
    have := hc.sum_profilePiece_mul_neutralize_eq_zero hσ hσne
    rw [hσeq] at this
    exact this
  disj := by
    intro ϱ hϱ ϱ' hϱ' hne t t' e
    have hc := rootedMarkedProfileContext_of_profileIndex hFzero hFsep hϱ t.1 t.2
    have hc' := rootedMarkedProfileContext_of_profileIndex hFzero hFsep hϱ' t'.1 t'.2
    have hσne : siteRestrict ϱ' ≠ siteRestrict ϱ := by
      intro h0
      apply hne
      rw [← (neutralize_siteRestrict_of_mem hϱ).2, ← h0, (neutralize_siteRestrict_of_mem hϱ').2]
    rcases le_total t'.1.1 t.1.1 with hle | hle
    · exact hc.grad_disjoint_cross hc' hL hσne hle e
    · exact (hc'.grad_disjoint_cross hc hL hσne.symm hle e).symm
  countG := by
    intro ϱ _
    have h := goodSelectedSum_le_three_mul ϱ
    rw [← card_profileIndex] at h
    simpa [Fintype.card_coe] using h

/-! ### Constancy of a profile on the other densities -/

/-- A profile piece takes one value on the face support of every other density of its family:
either it vanishes there, or that density lies in the collapse family and the potential is
constant on it. -/
theorem ProfileContext.profilePiece_eq_of_mem_other {F : Finset (ChargeDensity L)}
    {ρ : ChargeDensity L} {j : ℕ} {s : Finset (Generic.PinnedCharges.Site L)}
    {f : Generic.PinnedCharges.Site L → ℝ}
    (h : ProfileContext F ρ j s f) {σ : ChargeDensity L} (hσ : σ ∈ F) (hne : σ ≠ ρ)
    {x y : Generic.PinnedCharges.Site L} (hx : x ∈ chargeSupport σ)
    (hy : y ∈ chargeSupport σ) :
    profilePiece j f (some x) = profilePiece j f (some y) := by
  simp only [profilePiece_some]
  by_cases hex : ∃ z ∈ chargeSupport σ, profileRamp j (f z) ≠ 0
  · obtain ⟨z, hz, hz0⟩ := hex
    have hcol := h.mem_profileCollapseFamily_of_near_support hσ hne hz (h.near_of_ramp_ne_zero hz0)
    have hd := boundaryAdjustedSize_nonneg σ
    have hconst : ∀ w ∈ chargeSupport σ, f w = f z := by
      intro w hw
      refine eq_of_steps_in_ball (h.potential.collapse σ hcol) (y := z)
        (r := 8 * boundaryAdjustedSize σ + 2) (fun u hu => ?_) w ?_
      · rw [profileA3NeutralNeighborhood, mem_boundaryEnergyNeighborhood_iff]
        exact ⟨z, hz, by rw [siteDist_comm]; exact hu⟩
      · have h1 : euclideanSiteDistance w z ≤ chargeEuclideanDiameter σ := siteDist_le_diam hw hz
        have h2 := chargeEuclideanDiameter_le_boundaryAdjustedSize σ
        linarith
    rw [hconst x hx, hconst y hy]
  · push Not at hex
    rw [hex x hx, hex y hy]

/-! ### The clauses of the routine waves on a pinned separated family -/

section Routine

variable {α K₀ K₁ cP : ℝ} {F : Finset (ChargeDensity L)}

theorem mem_chargeSupport_of_mem_baseSites {ρ : ChargeDensity L}
    (x : {x // x ∈ baseSites (neutralizeAtWiredRoot ρ)}) : x.1 ∈ chargeSupport ρ := by
  have hx := x.2
  unfold baseSites at hx
  have h := (Finset.mem_filter.mp hx).2.1
  unfold chargeSupport
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using h⟩

/-- The routine wave of a member is orthogonal to every other member of the family. -/
theorem routineWave_orth (P : TerminalProfiles L α K₀ K₁ cP F) (hα : 1 < α) (hL : 1 < L)
    (hens : IsPinnedChargeEnsemble F) {ϱ : RotatorDualFace L → ℤ}
    (h : ϱ ∈ F.image neutralizeAtWiredRoot) (hϱ0 : ϱ ≠ 0) (hsum : ∑ j, ϱ j = 0)
    (t : (routineWave P hα hL ϱ h hϱ0 hsum).ι) {ϱ' : RotatorDualFace L → ℤ}
    (h' : ϱ' ∈ F.image neutralizeAtWiredRoot) (hne : ϱ' ≠ ϱ) :
    ∑ j, (routineWave P hα hL ϱ h hϱ0 hsum).piece t j * (ϱ' j : ℝ) = 0 := by
  rcases t with x | t
  · simp only [routineWave, Sum.elim_inl]
    rw [pairing_basePiece]
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp h'
    have hρσ : ρ ≠ σ := fun e => hne (e ▸ rfl)
    have hxρ : x.1 ∈ chargeSupport ρ := mem_chargeSupport_of_mem_baseSites x
    have hd := hens.2 ρ hρ σ hσ hρσ
    have hxσ : x.1 ∉ chargeSupport σ := Finset.disjoint_left.mp hd hxρ
    have : σ x.1 = 0 := by unfold chargeSupport at hxσ; simpa using hxσ
    simp [this]
  · exact P.orth ϱ h t ϱ' h' hne

/-- Two sites of distinct members of a pinned separated family are not neighbours. -/
theorem l1_ne_one_of_separated (hens : IsPinnedChargeEnsemble F)
    (hsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {ρ σ : ChargeDensity L} (hρ : ρ ∈ F) (hσ : σ ∈ F) (hρσ : ρ ≠ σ) {x y : Generic.PinnedCharges.Site L}
    (hx : x ∈ chargeSupport ρ) (hy : y ∈ chargeSupport σ) : l1 x y ≠ 1 := by
  intro h1
  have hd : euclideanSetDistance (chargeSupport ρ) (chargeSupport σ) ≤ 1 := by
    have := (setDist_le_siteDist hx hy).trans (siteDist_le_l1 x y)
    rw [h1] at this
    simpa using this
  have hs := hsep ρ hρ σ hσ hρσ
  have hmin : 1 ≤ min (boundaryAdjustedSize ρ) (boundaryAdjustedSize σ) :=
    le_min (one_le_boundaryAdjustedSize (hens.1 ρ hρ)) (one_le_boundaryAdjustedSize (hens.1 σ hσ))
  have hpow := le_rpow_self hmin one_le_chargeCoverExponent
  have hM : (chargeCoverScale : ℝ) = 65536 := by norm_num [chargeCoverScale]
  rw [hM] at hs
  linarith

/-- The routine waves of distinct members have pieces with disjoint gradients. -/
theorem routineWave_grad_disjoint_cross (P : TerminalProfiles L α K₀ K₁ cP F) (hα : 1 < α)
    (hL : 1 < L) (hens : IsPinnedChargeEnsemble F)
    (hsep : IsBoundarySeparated (chargeCoverScale : ℝ) chargeCoverExponent F)
    {ϱ ϱ' : RotatorDualFace L → ℤ}
    (h : ϱ ∈ F.image neutralizeAtWiredRoot) (hϱ0 : ϱ ≠ 0) (hsum : ∑ j, ϱ j = 0)
    (h' : ϱ' ∈ F.image neutralizeAtWiredRoot) (hϱ0' : ϱ' ≠ 0) (hsum' : ∑ j, ϱ' j = 0)
    (hne : ϱ ≠ ϱ') (t : (routineWave P hα hL ϱ h hϱ0 hsum).ι)
    (t' : (routineWave P hα hL ϱ' h' hϱ0' hsum').ι) (e : SquareZeroBond L) :
    (squareZero L).grad ((routineWave P hα hL ϱ h hϱ0 hsum).piece t) e = 0 ∨
      (squareZero L).grad ((routineWave P hα hL ϱ' h' hϱ0' hsum').piece t') e = 0 := by
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp h
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp h'
  have hρσ : ρ ≠ σ := fun e => hne (e ▸ rfl)
  rcases t with x | t <;> rcases t' with x' | t'
  · by_contra hh
    push Not at hh
    have hxx : x.1 ≠ x'.1 := fun hx => Finset.disjoint_left.mp
      (hens.2 ρ hρ σ hσ hρσ) (mem_chargeSupport_of_mem_baseSites x)
      (hx ▸ mem_chargeSupport_of_mem_baseSites x')
    exact l1_ne_one_of_separated hens hsep hρ hσ hρσ (mem_chargeSupport_of_mem_baseSites x)
      (mem_chargeSupport_of_mem_baseSites x') (l1_eq_one_of_grad_basePiece hxx hh.1 hh.2)
  · by_cases hb : (squareZero L).grad (basePiece (neutralizeAtWiredRoot ρ) x.1) e = 0
    · exact Or.inl hb
    · exact Or.inr (P.avoid _ h' t' ρ hρ x.1 (mem_chargeSupport_of_mem_baseSites x) e
        (grad_basePiece_incident hb))
  · by_cases hb : (squareZero L).grad (basePiece (neutralizeAtWiredRoot σ) x'.1) e = 0
    · exact Or.inr hb
    · exact Or.inl (P.avoid _ h t σ hσ x'.1 (mem_chargeSupport_of_mem_baseSites x') e
        (grad_basePiece_incident hb))
  · exact P.disj _ h _ h' hne t t' e

/-- The half-mass, edge-count and piece-count data of a routine wave. -/
theorem routineWave_layerData (P : TerminalProfiles L α K₀ K₁ cP F) (hα : 1 < α) (hL : 1 < L)
    {ϱ : RotatorDualFace L → ℤ} (h : ϱ ∈ F.image neutralizeAtWiredRoot) (hϱ0 : ϱ ≠ 0)
    (hsum : ∑ j, ϱ j = 0) :
    let Wv := routineWave P hα hL ϱ h hϱ0 hsum
    ((1 / 2 : ℝ) * ∑ j, |(ϱ j : ℝ)| ≤
      ∑ t ∈ (letI := Wv.finite; Finset.univ.filter fun t => Wv.scale t = 0), |Wv.charge t|) ∧
    (∀ t, ((Finset.univ.filter fun e => (squareZero L).grad (Wv.piece t) e ≠ 0).card : ℝ) ≤
      100 * 4 ^ Wv.scale t) ∧
    ((letI := Wv.finite; (Finset.univ.filter fun t => 1 ≤ Wv.scale t).card : ℕ) : ℝ) =
      Fintype.card (P.ι ϱ) := by
  intro Wv
  have hbase : ∀ x ∈ baseSites ϱ, ϱ (some x) ≠ 0 := fun x hx => by
    unfold baseSites at hx
    exact (Finset.mem_filter.mp hx).2.1
  refine ⟨?_, ?_, ?_⟩
  · have hm := half_mass_le_base ϱ hsum
    refine hm.trans (le_of_eq ?_)
    show _ = ∑ t ∈ (Finset.univ : Finset ({x // x ∈ baseSites ϱ} ⊕ P.ι ϱ)).filter
      (fun t => Sum.elim (fun _ => 0) (P.scale ϱ) t = 0),
        |Sum.elim (fun x => 2 * |(ϱ (some x.1) : ℝ)|) (P.charge ϱ) t|
    rw [Finset.sum_filter, Fintype.sum_sum_type]
    have h2 : ∑ t : P.ι ϱ, (if Sum.elim (fun _ => 0) (P.scale ϱ)
        (Sum.inr t : {x // x ∈ baseSites ϱ} ⊕ P.ι ϱ) = 0 then
        |Sum.elim (fun x => 2 * |(ϱ (some x.1) : ℝ)|) (P.charge ϱ)
          (Sum.inr t : {x // x ∈ baseSites ϱ} ⊕ P.ι ϱ)| else 0) = 0 :=
      Finset.sum_eq_zero fun t _ => ite_eq_right_iff.mpr fun h0 =>
        absurd h0 (show ¬ P.scale ϱ t = 0 by have := P.one_le_scale ϱ h t; omega)
    rw [h2, add_zero, ← Finset.sum_coe_sort (baseSites ϱ)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [abs_mul]
  · intro t
    rcases t with x | t
    · simp only [Wv, routineWave, Sum.elim_inl, pow_zero, mul_one]
      refine le_trans ?_ (show ((4 : ℕ) : ℝ) ≤ 100 by norm_num)
      exact_mod_cast (Finset.card_le_card fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        grad_basePiece_incident (Finset.mem_filter.mp he).2⟩).trans (card_incident_le_four x.1)
    · exact P.edge_count ϱ h t
  · show (((Finset.univ : Finset ({x // x ∈ baseSites ϱ} ⊕ P.ι ϱ)).filter fun t =>
        1 ≤ Sum.elim (fun _ => 0) (P.scale ϱ) t).card : ℝ) = Fintype.card (P.ι ϱ)
    rw [Finset.card_filter, Fintype.sum_sum_type]
    have h1 : ∑ x : {x // x ∈ baseSites ϱ}, (if 1 ≤ Sum.elim (fun _ => 0) (P.scale ϱ)
        (Sum.inl x : {x // x ∈ baseSites ϱ} ⊕ P.ι ϱ) then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun x _ => by simp
    have h2 : ∑ t : P.ι ϱ, (if 1 ≤ Sum.elim (fun _ => 0) (P.scale ϱ)
        (Sum.inr t : {x // x ∈ baseSites ϱ} ⊕ P.ι ϱ) then 1 else 0) = Fintype.card (P.ι ϱ) := by
      rw [Finset.card_univ.symm, Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl fun t _ => ite_eq_left_iff.mpr fun h0 =>
        absurd (P.one_le_scale ϱ h t) h0
    rw [h1, h2, zero_add]

end Routine

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
