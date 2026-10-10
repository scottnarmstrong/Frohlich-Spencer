/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3Path
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileAPotential

/-! # Terminal-specific geometry for the collapsed profile family

This module extracts the exact scale and separation information available for
`profileCollapseFamily` on a comb terminal and a charged selected square. -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- Every point of a charged restriction belongs to the support of its parent density. -/
theorem profileA3_restriction_support_subset (ρ : ChargeDensity L) (s : Finset (Site L)) :
    chargeSupport (chargeRestriction ρ s) ⊆ chargeSupport ρ := by
  intro x hx
  exact (mem_chargeSupport_restriction_iff ρ s x).mp hx |>.2

/-- The collapse-family size cutoff and the charged selected-square size imply that each
collapsed density is smaller than its charged parent. -/
theorem profileA3_collapse_size_lt_parent
    (j : ℕ) (ρ σ : ChargeDensity L)
    (hρ : (2 : ℝ) ^ (j + 1) ≤ boundaryAdjustedSize ρ)
    (hσ0 : σ ≠ 0)
    (hsmall : (chargeCoverScale : ℝ) * boundaryAdjustedSize σ ^ chargeCoverExponent ≤
      5 * 2 ^ j) :
    boundaryAdjustedSize σ < boundaryAdjustedSize ρ := by
  have hdσ : 1 ≤ boundaryAdjustedSize σ := one_le_boundaryAdjustedSize hσ0
  have hscale : (chargeCoverScale : ℝ) = 65536 := chargeCoverScale_eq
  have hα : chargeCoverExponent = (7 / 4 : ℝ) := rfl
  have hpow : boundaryAdjustedSize σ ≤ boundaryAdjustedSize σ ^ chargeCoverExponent :=
    Real.self_le_rpow_of_one_le hdσ (by rw [hα]; norm_num)
  have hσbound : boundaryAdjustedSize σ < (2 : ℝ) ^ j := by
    by_contra hn
    have hle : (2 : ℝ) ^ j ≤ boundaryAdjustedSize σ := le_of_not_gt hn
    rw [hscale, hα] at hsmall
    have hbig : (65536 : ℝ) * (2 : ℝ) ^ j ≤
        (65536 : ℝ) * boundaryAdjustedSize σ ^ (7 / 4 : ℝ) := by
      exact mul_le_mul_of_nonneg_left (le_trans hle hpow) (by norm_num)
    have hjPos : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) _
    nlinarith
  have hparent : (2 : ℝ) ^ j < boundaryAdjustedSize ρ := by
    have : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
    rw [this] at hρ
    linarith
  exact lt_trans hσbound hparent

/-- Data forced on one member of the exact collapse family by the terminal hypotheses.  In
particular, its scale is below the selected parent scale and its Appendix-D separation from the
parent support is measured by its own size. -/
theorem profileA3_terminal_collapse_member_data
    (N : ℕ) (T : SelConfig L) (hT : IsCombTerminal N T)
    (ρ : ChargeDensity L) (hρ : ρ ∈ T.F) (j : ℕ)
    (s : Finset (Site L)) (hs : s ∈ selectedSquares (neutralizeAtWiredRoot ρ) j)
    (hq : totalCharge (chargeRestriction ρ s) ≠ 0)
    (σ : ChargeDensity L)
    (hσ : σ ∈ profileCollapseFamily T.F ρ j
      (chargeSupport (chargeRestriction ρ s))) :
    σ ∈ T.F ∧ σ ≠ ρ ∧ totalCharge σ = 0 ∧ σ ≠ 0 ∧
      boundaryAdjustedSize σ < boundaryAdjustedSize ρ ∧
      (65536 : ℝ) * boundaryAdjustedSize σ ^ (7 / 4 : ℝ) ≤ 5 * 2 ^ j ∧
      (65526 : ℝ) * boundaryAdjustedSize σ ^ (7 / 4 : ℝ) ≤ (9 / 4 : ℝ) * 2 ^ j ∧
      (65536 : ℝ) * boundaryAdjustedSize σ ^ (7 / 4 : ℝ) ≤
        euclideanSetDistance (chargeSupport (chargeRestriction ρ s)) (chargeSupport σ) := by
  classical
  have hσmem := Finset.mem_filter.mp hσ
  have hσF : σ ∈ T.F := hσmem.1
  obtain ⟨hne, hneutral, hsmall, hnear⟩ := hσmem.2
  have hσ0 : σ ≠ 0 := hT.geometry.ensemble.1 σ hσF
  have hSq := chargedSelectedSquare_of_mem hs hq
  have hsize := profileA3_collapse_size_lt_parent j ρ σ hSq.size hσ0 (by
    simpa [chargeCoverScale_eq, (show chargeCoverExponent = (7 / 4 : ℝ) from rfl)] using hsmall)
  have hparentSubset := profileA3_restriction_support_subset ρ s
  have hKne : (chargeSupport (chargeRestriction ρ s)).Nonempty :=
    chargeSupport_nonempty_of_ne_zero _ (by
      intro hzero
      exact hq (by simp [hzero, totalCharge]))
  have hpair := hT.geometry.separated ρ hρ σ hσF (Ne.symm hne)
  have hparentSep : (65536 : ℝ) * boundaryAdjustedSize σ ^ (7 / 4 : ℝ) ≤
      euclideanSetDistance (chargeSupport (chargeRestriction ρ s)) (chargeSupport σ) := by
    have hpair' := setDist_le_of_subset hparentSubset subset_rfl hKne
      (chargeSupport_nonempty_of_ne_zero σ hσ0)
    have hmin : min (boundaryAdjustedSize ρ) (boundaryAdjustedSize σ) =
        boundaryAdjustedSize σ := min_eq_right hsize.le
    rw [chargeCoverScale_eq, show chargeCoverExponent = (7 / 4 : ℝ) from rfl, hmin] at hpair
    exact hpair.trans hpair'
  have hnear' : (profileA3NeutralNeighborhood σ ∩
      boundaryEnergyNeighborhood ((9 / 4 : ℝ) * 2 ^ j)
        (chargeSupport (chargeRestriction ρ s))).Nonempty := by
    simpa [profileA3NeutralNeighborhood] using hnear
  have hnearScale := profileA3_nearby_neutral_scale_bound
    (65536 : ℝ) (7 / 4 : ℝ) ((9 / 4 : ℝ) * 2 ^ j) T.F ρ σ
    (chargeSupport (chargeRestriction ρ s)) hT.geometry.separated hρ hσF
    (Ne.symm hne) hσ0 hparentSubset hsize.le (by norm_num) hnear'
  refine ⟨hσF, hne, hneutral, hσ0, hsize, ?_, ?_, hparentSep⟩
  · simpa [chargeCoverScale_eq, show chargeCoverExponent = (7 / 4 : ℝ) from rfl] using hsmall
  · simpa [show (65536 : ℝ) - 10 = 65526 by norm_num] using hnearScale

/-- Pairwise expanded-neighborhood separation in the exact family used by a terminal profile.
The radius losses are left explicit for the max-scale component induction. -/
theorem profileA3_terminal_collapse_neighborhood_separation
    (N : ℕ) (T : SelConfig L) (hT : IsCombTerminal N T)
    (ρ : ChargeDensity L) (_hρ : ρ ∈ T.F) (j : ℕ) (K : Finset (Site L))
    {σ τ : ChargeDensity L}
    (hσ : σ ∈ profileCollapseFamily T.F ρ j K)
    (hτ : τ ∈ profileCollapseFamily T.F ρ j K) (hne : σ ≠ τ) :
    (65536 : ℝ) * min (boundaryAdjustedSize σ) (boundaryAdjustedSize τ) ^ (7 / 4 : ℝ) ≤
      euclideanSetDistance (profileA3NeutralNeighborhood σ)
        (profileA3NeutralNeighborhood τ) +
        (8 * boundaryAdjustedSize σ + 2) + (8 * boundaryAdjustedSize τ + 2) := by
  classical
  have hσmem := Finset.mem_filter.mp hσ
  have hτmem := Finset.mem_filter.mp hτ
  have hσF : σ ∈ T.F := hσmem.1
  have hτF : τ ∈ T.F := hτmem.1
  have hσ0 : σ ≠ 0 := hT.geometry.ensemble.1 σ hσF
  have hτ0 : τ ≠ 0 := hT.geometry.ensemble.1 τ hτF
  have hsep := hT.geometry.separated σ hσF τ hτF hne
  simpa [chargeCoverScale_eq,
    show chargeCoverExponent = (7 / 4 : ℝ) from rfl] using
    (profileA3_separated_neighborhoods (65536 : ℝ) (7 / 4 : ℝ) σ τ hσ0 hτ0
    (by simpa [chargeCoverScale_eq,
      show chargeCoverExponent = (7 / 4 : ℝ) from rfl] using hsep))

/-- The exact remaining construction required by the terminal consumer: a path-packing certificate
for the actual collapsed potential, for every charged selected square and every endpoint, at the
scales where the collapse family can be nonempty. -/
def TerminalProfileA3PathCertificatesLarge : Prop :=
  ∀ (L N : ℕ) (T : SelConfig L), IsCombTerminal N T → ∀ ρ ∈ T.F,
    ∀ j ∈ Finset.Icc 14 (layerCutoff (neutralizeAtWiredRoot ρ)),
    ∀ s ∈ selectedSquares (neutralizeAtWiredRoot ρ) j,
      totalCharge (chargeRestriction ρ s) ≠ 0 →
        ∀ x, Nonempty (ProfileA3PathWitness
          (chargeSupport (chargeRestriction ρ s))
          (profileCollapsedPotential T.F ρ j
            (chargeSupport (chargeRestriction ρ s))) x)

/-- The terminal path-certificate constructor feeds the exact large-scale support clause consumed
by `TerminalProfileAPotential`. -/
theorem terminalCollapsedSupportControlLarge_of_pathCertificates
    (h : TerminalProfileA3PathCertificatesLarge) : TerminalCollapsedSupportControlLarge := by
  intro L N T hT ρ hρ j hj s hs hq
  exact profileA3CollapsedSupportControl_of_path_witness j
    (chargeSupport (chargeRestriction ρ s))
    (profileCollapsedPotential T.F ρ j (chargeSupport (chargeRestriction ρ s)))
    (h L N T hT ρ hρ j hj s hs hq)

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
