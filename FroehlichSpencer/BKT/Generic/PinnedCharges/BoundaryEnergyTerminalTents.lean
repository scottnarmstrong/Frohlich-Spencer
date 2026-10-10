/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyTent
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergySelection

/-! # Tents on all terminal selection branches -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- Every square retained on every terminal branch has a nonzero integer
charge and its charge-support tent has pairing magnitude at least one. -/
theorem exists_selectionExpansion_with_childTents
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
          scaleBoundaryMargin j ≤
            euclideanBoundaryDistance (chargeSupport (chargeRestriction ρ s)) ∧
          1 ≤ |∑ x, boundaryEnergyTent
            (chargeSupport (chargeRestriction ρ s)) ((2 : ℝ) ^ j) x * (ρ x : ℝ)| := by
  obtain ⟨B, hB⟩ := SelectionG.exists_selectionExpansion_of_singleSites
    hMiso hα hE hsingle K
  refine ⟨B, hB, ?_⟩
  intro b hb ρ hρ j C hC s hs
  rcases hB.1 b hb with ⟨_, hgeom⟩
  have hcharge := boundaryEnergy_selectedSquare_charge Miso Msel α
    (by linarith) (by linarith) hmargin j ρ b.2.1 hgeom.isolated hρ C hC s hs
  have hclear := boundaryEnergy_selectedSquare_boundaryClearance Msel α j ρ C hC s hs
  have hpair := boundaryEnergy_selectedChildTent_pairing_abs_ge_one Miso Msel α
    (by linarith) (by linarith) hα hMsel hmargin j ρ b.2.1 hgeom.isolated hρ
    C hC s hs
  exact ⟨hcharge, hclear, hpair⟩

/-- A fine selected square belongs to the clipped KP carrier, so the
at-most-one-coarse overlap lemma applies directly to it. -/
theorem terminal_selectedSquare_at_most_one_coarse
    (ρ : ChargeDensity L) (j k : ℕ) (hjk : j < k)
    (Cj Ck : Finset (Finset (Site L)))
    (hCj : IsMinimumSquareCover .free L j ρ Cj)
    (hCk : IsMinimumSquareCover .free L k ρ Ck)
    {s t₁ t₂ : Finset (Site L)}
    (hs : s ∈ pinnedPPrime chargeCoverScale chargeCoverExponent j ρ Cj)
    (ht₁ : t₁ ∈ pinnedPPrime chargeCoverScale chargeCoverExponent k ρ Ck)
    (ht₂ : t₂ ∈ pinnedPPrime chargeCoverScale chargeCoverExponent k ρ Ck)
    (ht₁₂ : t₁ ≠ t₂)
    (hcoarse₁ : (boundaryEnergyNeighborhood (2 * (2 : ℝ) ^ j) s ∩
      boundaryEnergyNeighborhood (2 * (2 : ℝ) ^ k) t₁).Nonempty)
    (hcoarse₂ : (boundaryEnergyNeighborhood (2 * (2 : ℝ) ^ j) s ∩
      boundaryEnergyNeighborhood (2 * (2 : ℝ) ^ k) t₂).Nonempty) : False := by
  have hsSquare := (pinnedPPrime_mem_of_minimumCover chargeCoverScale
    chargeCoverExponent j ρ Cj hCj hs).2
  exact boundaryEnergy_terminalNeighborhood_at_most_one_coarse j k hjk s t₁ t₂
    Ck ρ hCk ht₁ ht₂ ht₁₂ hsSquare hcoarse₁ hcoarse₂

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
