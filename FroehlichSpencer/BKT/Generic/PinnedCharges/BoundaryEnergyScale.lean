/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyTerminalTents

/-! # Signed local profiles at a fixed scale

The signs of the selected-square tents are chosen from their charge pairings.
This makes the pairing of their sum additive and nonnegative, without imposing
an orientation convention on the individual charge restrictions.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT.Rotator

variable {L : ℕ}

/-- Pairing of the support-centered tent for a selected square with the parent
charge. -/
def boundaryEnergyChildTentPairing (ρ : ChargeDensity L)
    (s : Finset (Site L)) (r : ℝ) : ℝ :=
  ∑ x, boundaryEnergyTent (chargeSupport (chargeRestriction ρ s)) r x * (ρ x : ℝ)

/-- The sign that orients a support-centered tent positively against its
parent charge. -/
def boundaryEnergyChildTentSign (ρ : ChargeDensity L)
    (s : Finset (Site L)) (r : ℝ) : ℝ :=
  if 0 ≤ boundaryEnergyChildTentPairing ρ s r then 1 else -1

/-- A signed support-centered tent, pinned to zero at the wired vertex. -/
def boundaryEnergySignedChildTent (ρ : ChargeDensity L)
    (s : Finset (Site L)) (r : ℝ) : RotatorDualFace L → ℝ
  | none => 0
  | some x => boundaryEnergyChildTentSign ρ s r *
      boundaryEnergyTent (chargeSupport (chargeRestriction ρ s)) r x

/-- The positively oriented sum of support-centered tents for one selected
family. -/
def boundaryEnergyScaleField (ρ : ChargeDensity L)
    (P : Finset (Finset (Site L))) (r : ℝ) : RotatorDualFace L → ℝ := fun z =>
  ∑ s ∈ P, boundaryEnergySignedChildTent ρ s r z

theorem boundaryEnergyChildTentSign_mul_pairing_ge_one
    (ρ : ChargeDensity L) (s : Finset (Site L)) (r : ℝ)
    (hpair : 1 ≤ |boundaryEnergyChildTentPairing ρ s r|) :
    1 ≤ boundaryEnergyChildTentSign ρ s r *
      boundaryEnergyChildTentPairing ρ s r := by
  unfold boundaryEnergyChildTentSign
  split_ifs with h
  · rw [abs_of_nonneg h] at hpair
    nlinarith
  · have hneg : boundaryEnergyChildTentPairing ρ s r < 0 := lt_of_not_ge h
    rw [abs_of_neg hneg] at hpair
    nlinarith

/-- At a fixed scale, orienting and summing all selected-square tents gives a
field whose pairing with the parent charge is at least the number of selected
squares. Boundary vanishing is inherited term by term. -/
theorem boundaryEnergyScaleField_properties
    (ρ : ChargeDensity L) (P : Finset (Finset (Site L))) (r : ℝ)
    (hpair : ∀ s ∈ P, 1 ≤ |boundaryEnergyChildTentPairing ρ s r|)
    (hboundary : ∀ s ∈ P, ∀ x : Site L, siteBoundaryDepth x = 1 →
      boundaryEnergyTent (chargeSupport (chargeRestriction ρ s)) r x = 0) :
    (boundaryEnergyScaleField ρ P r) none = 0 ∧
      (P.card : ℝ) ≤
        ∑ x, (boundaryEnergyScaleField ρ P r) (some x) * (ρ x : ℝ) ∧
      ∀ x : Site L, siteBoundaryDepth x = 1 →
        (boundaryEnergyScaleField ρ P r) (some x) = 0 := by
  classical
  let U := boundaryEnergyScaleField ρ P r
  change U none = 0 ∧
    (P.card : ℝ) ≤ ∑ x, U (some x) * (ρ x : ℝ) ∧
    (∀ x : Site L, siteBoundaryDepth x = 1 → U (some x) = 0)
  refine ⟨?_, ?_, ?_⟩
  · simp [U, boundaryEnergyScaleField, boundaryEnergySignedChildTent]
  · have hpairSum : (∑ s ∈ P, (1 : ℝ)) ≤
        ∑ s ∈ P, boundaryEnergyChildTentSign ρ s r *
          boundaryEnergyChildTentPairing ρ s r := by
      apply Finset.sum_le_sum
      intro s hs
      exact boundaryEnergyChildTentSign_mul_pairing_ge_one ρ s r (hpair s hs)
    have hexchange : (∑ x, U (some x) * (ρ x : ℝ)) =
        ∑ s ∈ P, boundaryEnergyChildTentSign ρ s r *
          boundaryEnergyChildTentPairing ρ s r := by
      calc
        (∑ x, U (some x) * (ρ x : ℝ)) =
            ∑ x, ∑ s ∈ P,
              boundaryEnergyChildTentSign ρ s r *
                boundaryEnergyTent (chargeSupport (chargeRestriction ρ s)) r x *
                  (ρ x : ℝ) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    simp only [U, boundaryEnergyScaleField, boundaryEnergySignedChildTent]
                    rw [Finset.sum_mul]
        _ = ∑ s ∈ P, ∑ x,
              boundaryEnergyChildTentSign ρ s r *
                boundaryEnergyTent (chargeSupport (chargeRestriction ρ s)) r x *
                  (ρ x : ℝ) := by rw [Finset.sum_comm]
        _ = ∑ s ∈ P, boundaryEnergyChildTentSign ρ s r *
              boundaryEnergyChildTentPairing ρ s r := by
                apply Finset.sum_congr rfl
                intro s hs
                unfold boundaryEnergyChildTentPairing
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x hx
                ring
    calc
      (P.card : ℝ) = ∑ s ∈ P, (1 : ℝ) := by simp
      _ ≤ ∑ s ∈ P, boundaryEnergyChildTentSign ρ s r *
          boundaryEnergyChildTentPairing ρ s r := hpairSum
      _ = ∑ x, U (some x) * (ρ x : ℝ) := hexchange.symm
  · intro x hx
    simp only [U, boundaryEnergyScaleField]
    apply Finset.sum_eq_zero
    intro s hs
    simp only [boundaryEnergySignedChildTent]
    rw [hboundary s hs x hx]
    ring

/-- Existential form of the fixed-scale profile construction. -/
theorem exists_boundaryEnergy_scaleProfile
    (ρ : ChargeDensity L) (P : Finset (Finset (Site L))) (r : ℝ)
    (hpair : ∀ s ∈ P, 1 ≤ |boundaryEnergyChildTentPairing ρ s r|)
    (hboundary : ∀ s ∈ P, ∀ x : Site L, siteBoundaryDepth x = 1 →
      boundaryEnergyTent (chargeSupport (chargeRestriction ρ s)) r x = 0) :
    ∃ U : RotatorDualFace L → ℝ, U none = 0 ∧
      (P.card : ℝ) ≤ ∑ x, U (some x) * (ρ x : ℝ) ∧
      ∀ x : Site L, siteBoundaryDepth x = 1 → U (some x) = 0 := by
  refine ⟨boundaryEnergyScaleField ρ P r, ?_⟩
  exact boundaryEnergyScaleField_properties ρ P r hpair hboundary

/-- The terminal-ensemble adapter supplies the fixed-scale pairing and pinned
boundary support for every square in `pinnedPPrime`. -/
theorem boundaryEnergyTerminalScaleField_properties
    (Miso Msel α : ℝ) (hMiso : 1 < Miso) (hα : 1 ≤ α)
    (hMsel : 1 ≤ Msel) (hmargin : Miso * (Real.sqrt 2) ^ α ≤ Msel)
    (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation Miso α N) (hρ : ρ ∈ N)
    (j : ℕ) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) :
    (boundaryEnergyScaleField ρ (pinnedPPrime Msel α j ρ C) ((2 : ℝ) ^ j)) none = 0 ∧
      ((pinnedPPrime Msel α j ρ C).card : ℝ) ≤
        ∑ x, (boundaryEnergyScaleField ρ
          (pinnedPPrime Msel α j ρ C) ((2 : ℝ) ^ j)) (some x) * (ρ x : ℝ) ∧
      ∀ x : Site L, siteBoundaryDepth x = 1 →
        (boundaryEnergyScaleField ρ
          (pinnedPPrime Msel α j ρ C) ((2 : ℝ) ^ j)) (some x) = 0 := by
  apply boundaryEnergyScaleField_properties
  · intro s hs
    exact boundaryEnergy_selectedChildTent_pairing_abs_ge_one Miso Msel α
      (by linarith) (by linarith) hα hMsel hmargin j ρ N hN hρ C hC s hs
  · intro s hs x hx
    have hclear := boundaryEnergy_selectedSquare_boundaryClearance Msel α j ρ C hC s hs
    have hcharge := boundaryEnergy_selectedSquare_charge Miso Msel α
      (by linarith) (by linarith) hmargin j ρ N hN hρ C hC s hs
    have hchildne : chargeRestriction ρ s ≠ 0 := by
      intro hz
      apply hcharge
      simp [totalCharge, hz]
    have hnonempty :
        (chargeSupport (chargeRestriction ρ s)).Nonempty :=
      chargeSupport_nonempty_of_ne_zero (chargeRestriction ρ s) hchildne
    exact boundaryEnergy_childTent_zero_at_boundary j
      (chargeSupport (chargeRestriction ρ s)) hnonempty hclear x hx

theorem exists_boundaryEnergy_terminalScaleProfile
    (Miso Msel α : ℝ) (hMiso : 1 < Miso) (hα : 1 ≤ α)
    (hMsel : 1 ≤ Msel) (hmargin : Miso * (Real.sqrt 2) ^ α ≤ Msel)
    (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation Miso α N) (hρ : ρ ∈ N)
    (j : ℕ) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) :
    ∃ U : RotatorDualFace L → ℝ, U none = 0 ∧
      ((pinnedPPrime Msel α j ρ C).card : ℝ) ≤
        ∑ x, U (some x) * (ρ x : ℝ) ∧
      ∀ x : Site L, siteBoundaryDepth x = 1 → U (some x) = 0 := by
  refine ⟨boundaryEnergyScaleField ρ (pinnedPPrime Msel α j ρ C) ((2 : ℝ) ^ j), ?_⟩
  exact boundaryEnergyTerminalScaleField_properties Miso Msel α hMiso hα
    hMsel hmargin ρ N hN hρ j C hC

/-- Terminal branches expose exactly the Appendix-D isolation clause needed
to build each selected scale profile. -/
theorem exists_boundaryEnergy_terminalScaleProfile_of_geometry
    (Miso Msel α : ℝ) (hMiso : 1 < Miso) (hα : 1 ≤ α)
    (hMsel : 1 ≤ Msel) (hmargin : Miso * (Real.sqrt 2) ^ α ≤ Msel)
    {N : Finset (ChargeDensity L)} (hgeom : AppendixDChargeGeometry Miso α N)
    {ρ : ChargeDensity L} (hρ : ρ ∈ N)
    (j : ℕ) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) :
    ∃ U : RotatorDualFace L → ℝ, U none = 0 ∧
      ((pinnedPPrime Msel α j ρ C).card : ℝ) ≤
        ∑ x, U (some x) * (ρ x : ℝ) ∧
      ∀ x : Site L, siteBoundaryDepth x = 1 → U (some x) = 0 := by
  exact exists_boundaryEnergy_terminalScaleProfile Miso Msel α hMiso hα hMsel
    hmargin ρ N hgeom.isolated hρ j C hC

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
