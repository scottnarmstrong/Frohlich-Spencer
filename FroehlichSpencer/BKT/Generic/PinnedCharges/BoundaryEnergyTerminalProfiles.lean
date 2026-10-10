/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyScale
public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGExpansion

/-! # Scale profiles on selection-expansion terminals -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG
open FroehlichSpencer.BKT.Rotator

variable {L : ℕ}

/-- Every density in every terminal branch admits a pinned, boundary-vanishing
scale profile whose charge pairing is at least the number of selected squares
at that scale. -/
theorem selectionExpansion_terminal_scaleProfile
    (Miso Msel α : ℝ) (hMiso : 1 < Miso) (hα : 1 ≤ α)
    (hMsel : 1 ≤ Msel) (hmargin : Miso * (Real.sqrt 2) ^ α ≤ Msel)
    {E : ChargeEnsemble L} {K : ChargeDensity L → ℝ}
    {B : List (Branch L)} (hB : IsSelectionExpansion Miso α E K B)
    (b : Branch L) (hb : b ∈ B) {ρ : ChargeDensity L} (hρ : ρ ∈ b.2.1)
    (j : ℕ) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) :
    ∃ U : RotatorDualFace L → ℝ, U none = 0 ∧
      ((pinnedPPrime Msel α j ρ C).card : ℝ) ≤
        ∑ x, U (some x) * (ρ x : ℝ) ∧
      ∀ x : Site L, siteBoundaryDepth x = 1 → U (some x) = 0 := by
  obtain ⟨_hweight, hgeom⟩ := hB.1 b hb
  exact exists_boundaryEnergy_terminalScaleProfile_of_geometry Miso Msel α
    hMiso hα hMsel hmargin hgeom hρ j C hC

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
