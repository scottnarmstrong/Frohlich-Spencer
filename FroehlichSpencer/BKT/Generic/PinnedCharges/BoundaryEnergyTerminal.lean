/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGExpansion
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyPairing

/-! # Boundary data on terminal selection ensembles

The terminal selection expansion supplies the isolation clause.  This module
applies it to every Appendix-D selected square, with separate constants for
the isolation and square-separation margins.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- The scale-selection expansion, together with the charge pairing and
boundary-clearance facts for every selected square of every terminal branch.
The larger `Msel` margin pays for the diagonal of a cover square; terminal
isolation is supplied at `Miso`. -/
theorem exists_selectionExpansion_with_boundaryEnergyData
    (Miso Msel α : ℝ) (hMiso : 1 < Miso) (hα : 1 ≤ α)
    (hMsel : 1 ≤ Msel) (hmargin : Miso * (Real.sqrt 2) ^ α ≤ Msel)
    {E : ChargeEnsemble L} (hE : IsPinnedChargeEnsemble E)
    (hsingle : ∀ ρ ∈ E, (chargeSupport ρ).card = 1)
    (K : ChargeDensity L → ℝ) :
    ∃ B, IsSelectionExpansion Miso α E K B ∧
      ∀ b ∈ B, ∀ ρ ∈ b.2.1, ∀ j (C : Finset (Finset (Site L))),
        IsMinimumSquareCover .free L j ρ C →
        ∀ s ∈ pinnedPPrime Msel α j ρ C,
          totalCharge (chargeRestriction ρ s) ≠ 0 ∧
            scaleBoundaryMargin j ≤ euclideanBoundaryDistance
              (chargeSupport (chargeRestriction ρ s)) ∧
            ∀ φ : Site L → ℝ,
              (∀ x ∈ s, φ x = 1) →
              (∀ x, x ∉ s →
                (∀ y ∈ s, (2 : ℝ) ^ j < euclideanSiteDistance y x) → φ x = 0) →
              1 ≤ |∑ x, φ x * (ρ x : ℝ)| := by
  obtain ⟨B, hB⟩ :=
    SelectionG.exists_selectionExpansion_of_singleSites hMiso hα hE hsingle K
  refine ⟨B, hB, ?_⟩
  intro b hb ρ hρ j C hC s hs
  rcases hB.1 b hb with ⟨_, hgeom⟩
  refine ⟨boundaryEnergy_selectedSquare_charge Miso Msel α
      (by linarith) (by linarith) hmargin j ρ b.2.1 hgeom.isolated hρ C hC s hs,
    boundaryEnergy_selectedSquare_boundaryClearance Msel α j ρ C hC s hs, ?_⟩
  intro φ hplateau hlocal
  exact boundaryEnergy_selectedSquare_pairing_abs_ge_one Miso Msel α
    (by linarith) (by linarith) hα hMsel hmargin j ρ b.2.1 hgeom.isolated hρ
    C hC s hs φ hplateau hlocal

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
