/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileAPiece

/-!
# Terminal profiles: the clauses between pieces and densities

* `avoid` (`grad_eq_zero_of_incident`): zero gradient on every edge at a charge of the ensemble.

At a cluster charge both ends lie in the flat core; at a charge of another density near the
  ramp, that density is in the collapse family and the edge lies in its `E_σ`; elsewhere the
  ramp vanishes on both ends.
* `orth` (`sum_profilePiece_mul_neutralize_eq_zero`): a density reaching the support of the ramp is
  in the collapse family, so the ramp is constant on its support, and the density is neutral.
* `grad_disjoint` within a density (`grad_disjoint_same`): same scale, distinct squares are `R_j`
  apart; scales `j' + 3 ≤ j`, a finer cluster near the coarser ramp lies in the coarser cluster
  (the selection separation), so the finer ramp's edges sit in the coarser flat core.
* `disj` across densities (`grad_disjoint_cross`): two ramps meeting at scales `j' ≤ j` put the
  finer density in the coarser one's collapse family, with the finer near set in its `E_σ`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

theorem mem_profileA3NeutralNeighborhood_of_l1 {σ : ChargeDensity L} {x u : Site L}
    (hx : x ∈ chargeSupport σ) (hxu : l1 x u ≤ 1) : u ∈ profileA3NeutralNeighborhood σ := by
  rw [profileA3NeutralNeighborhood, mem_boundaryEnergyNeighborhood_iff]
  refine ⟨x, hx, ?_⟩
  have h1 := siteDist_le_l1 x u
  have h2 : (l1 x u : ℝ) ≤ 1 := by exact_mod_cast hxu
  have h3 := boundaryAdjustedSize_nonneg σ
  linarith

section Cross

variable {F : Finset (ChargeDensity L)} {ρ : ChargeDensity L} {j : ℕ} {s : Finset (Site L)}
  {f : Site L → ℝ}

/-- The endpoints of an edge with a nonzero ramp gradient, with the site the edge is incident to. -/
theorem endpoint_eq_of_incident {e : SquareZeroBond L} {u v x : Site L}
    (hs : (squareZero L).src e = some u) (ht : (squareZero L).tgt e = some v)
    (hinc : (squareZero L).src e = some x ∨ (squareZero L).tgt e = some x) : x = u ∨ x = v := by
  rcases hinc with h | h
  · rw [hs] at h; exact Or.inl (Option.some.inj h).symm
  · rw [ht] at h; exact Or.inr (Option.some.inj h).symm

/-- **`avoid`**: zero gradient on every edge at a charge of the ensemble. -/
theorem ProfileContext.grad_eq_zero_of_incident (h : ProfileContext F ρ j s f) (hL : 1 < L)
    {σ : ChargeDensity L} (hσ : σ ∈ F) {x : Site L} (hx : x ∈ chargeSupport σ)
    {e : SquareZeroBond L}
    (hinc : (squareZero L).src e = some x ∨ (squareZero L).tgt e = some x) :
    (squareZero L).grad (profilePiece j f) e = 0 := by
  by_contra he
  obtain ⟨u, v, hs, ht, huv, hu, hv⟩ := h.exists_near_of_grad_ne_zero hL he
  have hxuv := endpoint_eq_of_incident hs ht hinc
  have hxnear : IsProfileNear ρ j s x := by
    rcases hxuv with rfl | rfl
    · exact h.near_of_lt hu
    · exact h.near_of_lt hv
  have hxu : l1 x u ≤ 1 := by
    rcases hxuv with rfl | rfl
    · rw [l1_self]; omega
    · rw [l1_comm, huv]
  have hxv : l1 x v ≤ 1 := by
    rcases hxuv with rfl | rfl
    · rw [huv]
    · rw [l1_self]; omega
  apply he
  rw [Multigraph.grad, hs, ht, profilePiece_some, profilePiece_some]
  by_cases hσρ : σ = ρ
  · subst hσρ
    have hxK := h.mem_cluster_of_near hxnear hx
    have hj2 := two_le_two_pow h.one_le
    have hu1 : profileRamp j (f u) = 1 := h.ramp_eq_one_of_l1 hxK (by
      have : (l1 u x : ℝ) ≤ 1 := by rw [l1_comm]; exact_mod_cast hxu
      linarith)
    have hv1 : profileRamp j (f v) = 1 := h.ramp_eq_one_of_l1 hxK (by
      have : (l1 v x : ℝ) ≤ 1 := by rw [l1_comm]; exact_mod_cast hxv
      linarith)
    rw [hu1, hv1, sub_self]
  · have hcol := h.mem_profileCollapseFamily_of_near_support hσ hσρ hx hxnear
    rw [h.potential.collapse σ hcol u (mem_profileA3NeutralNeighborhood_of_l1 hx hxu) v
      (mem_profileA3NeutralNeighborhood_of_l1 hx hxv) huv, sub_self]

/-- **`orth`**: the profile is orthogonal to every other density of the ensemble. -/
theorem ProfileContext.sum_profilePiece_mul_neutralize_eq_zero (h : ProfileContext F ρ j s f)
    {σ : ChargeDensity L} (hσ : σ ∈ F) (hne : σ ≠ ρ) :
    ∑ v, profilePiece j f v * (neutralizeAtWiredRoot σ v : ℝ) = 0 := by
  rw [Fintype.sum_option, profilePiece_none, zero_mul, zero_add]
  simp_rw [profilePiece_some, neutralizeAtWiredRoot_some]
  by_cases hex : ∃ z ∈ chargeSupport σ, profileRamp j (f z) ≠ 0
  · obtain ⟨z, hz, hz0⟩ := hex
    have hcol := h.mem_profileCollapseFamily_of_near_support hσ hne hz (h.near_of_ramp_ne_zero hz0)
    have hQ : totalCharge σ = 0 := (Finset.mem_filter.mp hcol).2.2.1
    have hd := boundaryAdjustedSize_nonneg σ
    have hconst : ∀ x ∈ chargeSupport σ, f x = f z := by
      intro x hx
      refine eq_of_steps_in_ball (h.potential.collapse σ hcol) (y := z)
        (r := 8 * boundaryAdjustedSize σ + 2) (fun w hw => ?_) x ?_
      · rw [profileA3NeutralNeighborhood, mem_boundaryEnergyNeighborhood_iff]
        exact ⟨z, hz, by rw [siteDist_comm]; exact hw⟩
      · have h1 : euclideanSiteDistance x z ≤ chargeEuclideanDiameter σ := siteDist_le_diam hx hz
        have h2 := chargeEuclideanDiameter_le_boundaryAdjustedSize σ
        linarith
    calc ∑ x, profileRamp j (f x) * (σ x : ℝ) = ∑ x, profileRamp j (f z) * (σ x : ℝ) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : x ∈ chargeSupport σ
          · rw [hconst x hx]
          · have : σ x = 0 := by simpa [chargeSupport] using hx
            simp [this]
      _ = profileRamp j (f z) * (totalCharge σ : ℝ) := by
          rw [← Finset.mul_sum]; unfold totalCharge; push_cast; rfl
      _ = 0 := by rw [hQ, Int.cast_zero, mul_zero]
  · push Not at hex
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x ∈ chargeSupport σ
    · rw [hex x hx, zero_mul]
    · have : σ x = 0 := by simpa [chargeSupport] using hx
      simp [this]

/-- A site near both a coarse cluster and a finer cluster (`j' + 3 ≤ j`) of the same density is in
the coarse flat core. -/
theorem ProfileContext.ramp_eq_one_of_near_finer (h : ProfileContext F ρ j s f) {j' : ℕ}
    {s' : Finset (Site L)} (hjj : j' + 3 ≤ j) {w : Site L} (hw : IsProfileNear ρ j s w) (hw' : IsProfileNear ρ j' s' w) :
    profileRamp j (f w) = 1 := by
  obtain ⟨k, hk, hwk⟩ := hw
  obtain ⟨k', hk', hwk'⟩ := hw'
  have hp : (0 : ℝ) < 2 ^ j' := by positivity
  have hpj : (2 : ℝ) ^ j' * 8 ≤ 2 ^ j := by
    calc (2 : ℝ) ^ j' * 8 = 2 ^ (j' + 3) := by ring
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hjj
  have hk'ρ := (cluster_subset hk').2
  have hk's : k' ∈ s := by
    by_contra hk's
    have h1 := h.square.far k hk k' hk'ρ hk's
    have h2 := two_pow_le_selectionSeparation j
    have h3 := euclideanSiteDistance_triangle k w k'
    rw [siteDist_comm k w] at h3
    linarith
  have hk'K : k' ∈ chargeSupport (chargeRestriction ρ s) :=
    (mem_chargeSupport_restriction_iff ρ s k').mpr ⟨hk's, hk'ρ⟩
  refine h.ramp_eq_one_of_l1 hk'K ?_
  have := l1_le_three_halves_siteDist w k'
  linarith

/-- **`grad_disjoint` within a density**: distinct squares of one scale, or scales `j' + 3 ≤ j`. -/
theorem ProfileContext.grad_disjoint_same (h : ProfileContext F ρ j s f) {j' : ℕ}
    {s' : Finset (Site L)} {f' : Site L → ℝ} (h' : ProfileContext F ρ j' s' f') (hL : 1 < L)
    (hsep : (j = j' ∧ s ≠ s') ∨ j' + 3 ≤ j) (e : SquareZeroBond L) :
    (squareZero L).grad (profilePiece j f) e = 0 ∨
      (squareZero L).grad (profilePiece j' f') e = 0 := by
  by_contra hboth
  push Not at hboth
  obtain ⟨u, v, hs, ht, -, hu, hv⟩ := h.exists_near_of_grad_ne_zero hL hboth.1
  obtain ⟨u', v', hs', ht', -, hu', hv'⟩ := h'.exists_near_of_grad_ne_zero hL hboth.2
  rw [hs] at hs'
  rw [ht] at ht'
  obtain rfl := Option.some.inj hs'
  obtain rfl := Option.some.inj ht'
  rcases hsep with ⟨rfl, hss⟩ | hjj
  · obtain ⟨k, hk, huk⟩ := h.near_of_lt hu
    obtain ⟨k', hk', huk'⟩ := h'.near_of_lt hu'
    have h1 := selectionSeparation_le_of_ne h.selected h'.selected hss (cluster_subset hk).1
      (cluster_subset hk').1
    have h2 := two_pow_le_selectionSeparation j
    have h3 := euclideanSiteDistance_triangle k u k'
    rw [siteDist_comm k u] at h3
    have : (0 : ℝ) < 2 ^ j := by positivity
    linarith
  · apply hboth.1
    rw [Multigraph.grad, hs, ht, profilePiece_some, profilePiece_some,
      h.ramp_eq_one_of_near_finer hjj (h.near_of_lt hu) (h'.near_of_lt hu'),
      h.ramp_eq_one_of_near_finer hjj (h.near_of_lt hv) (h'.near_of_lt hv'), sub_self]

/-- **`disj` across densities**: profiles of distinct densities at scales `j' ≤ j`. -/
theorem ProfileContext.grad_disjoint_cross (h : ProfileContext F ρ j s f) {σ : ChargeDensity L}
    {j' : ℕ} {s' : Finset (Site L)} {f' : Site L → ℝ} (h' : ProfileContext F σ j' s' f')
    (hL : 1 < L) (hne : σ ≠ ρ) (hjj : j' ≤ j) (e : SquareZeroBond L) :
    (squareZero L).grad (profilePiece j f) e = 0 ∨
      (squareZero L).grad (profilePiece j' f') e = 0 := by
  by_contra hboth
  push Not at hboth
  obtain ⟨u, v, hs, ht, huv, hu, hv⟩ := h.exists_near_of_grad_ne_zero hL hboth.1
  obtain ⟨u', v', hs', ht', -, hu', hv'⟩ := h'.exists_near_of_grad_ne_zero hL hboth.2
  rw [hs] at hs'
  rw [ht] at ht'
  obtain rfl := Option.some.inj hs'
  obtain rfl := Option.some.inj ht'
  obtain ⟨hcol, hE⟩ := h.mem_profileCollapseFamily_of_near_near h' hne hjj (h.near_of_lt hu)
    (h'.near_of_lt hu')
  apply hboth.1
  rw [Multigraph.grad, hs, ht, profilePiece_some, profilePiece_some,
    h.potential.collapse σ hcol u (hE u (h'.near_of_lt hu')) v (hE v (h'.near_of_lt hv')) huv,
    sub_self]

end Cross

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
