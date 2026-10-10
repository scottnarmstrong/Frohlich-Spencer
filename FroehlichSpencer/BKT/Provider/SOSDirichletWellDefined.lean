/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.SOSDirichlet
public import FroehlichSpencer.BKT.Surface.SOSDirichletLaw
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.isProbabilityMeasure_sosDirichletLaw`

-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site siteBoundaryDepth euclideanSiteDistance)
open FroehlichSpencer.BKT.SOS.Roughening (sosHeightWeight sosHeightWeight_pos sosPartition
  sosVariance pinnedGrad pinnedField linfDist)
open FroehlichSpencer.BKT.Bridge.SOSDirichlet

/-- **The gate.** -/
theorem isProbabilityMeasure_sosDirichletLaw (L : ℕ) (β : ℝ) (hβ : 0 < β) :
    IsProbabilityMeasure (sosDirichletLaw L β hβ) := by
  have hpos := tsum_dirichletWeight_pos L hβ
  rw [sosDirichletLaw_eq]
  constructor
  rw [Measure.smul_apply, smul_eq_mul, dirichletMass_univ L hβ]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top

end FroehlichSpencer.BKT.Provider

end
