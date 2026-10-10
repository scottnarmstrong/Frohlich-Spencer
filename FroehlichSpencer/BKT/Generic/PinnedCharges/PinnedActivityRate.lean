/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.Activity

/-! # Arbitrarily strong activity powers from boundary estimates

Once the boundary entropy, Green-energy and cover-growth inequalities are available with fixed
positive rates, the exponent in the activity estimate can be made arbitrarily large by increasing
the inverse temperature. This file formalizes that final quantitative implication; it does not
derive the three boundary estimates.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open Real

/-- For any prescribed power `R`, sufficiently large inverse temperature upgrades the existing
boundary activity arithmetic to `exp(-R log dΛ)`. The threshold is explicit in the three rates. -/
theorem renormalizedActivity_le_any_boundary_power
    (β entropy energy area entropyRate energyRate areaRate R dΛ : ℝ)
    (hβ : 0 ≤ β) (hdΛ : 1 ≤ dΛ)
    (hEntropy : entropy ≤ entropyRate * area)
    (hEnergy : energyRate * area ≤ energy)
    (hArea : areaRate * Real.log dΛ ≤ area)
    (hR : 0 ≤ R) (hEnergyRate : 0 < energyRate) (hAreaRate : 0 < areaRate)
    (hThreshold : (R / areaRate + entropyRate) / energyRate ≤ β) :
    Real.exp (entropy - β * energy) ≤ Real.exp (-R * Real.log dΛ) := by
  have hscale : R / areaRate + entropyRate ≤ β * energyRate := by
    have hmul := (div_le_iff₀ hEnergyRate).mp hThreshold
    linarith
  have hRdiv : 0 ≤ R / areaRate := div_nonneg hR hAreaRate.le
  have hnet : 0 ≤ β * energyRate - entropyRate := by linarith
  have hrate : R / areaRate ≤ β * energyRate - entropyRate := by linarith
  have hgain : R ≤ areaRate * (β * energyRate - entropyRate) := by
    have hmul := (div_le_iff₀ hAreaRate).mp hrate
    nlinarith [hmul]
  exact renormalizedActivity_le_boundaryDecay β entropy energy area entropyRate energyRate
    areaRate R dΛ hβ hdΛ hEntropy hEnergy hArea hnet hgain

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
