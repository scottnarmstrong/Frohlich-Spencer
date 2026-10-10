/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.Geometry
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Boundary activity arithmetic

This is the final elementary implication in the Appendix D activity estimate.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

/-- Convert separate entropy and local-energy estimates into logarithmic
boundary decay.  `areaLower` is the charge-cover estimate
`K log dΛ ≤ A`; `gainLower` chooses a low-temperature exponent no larger than
`K (βD − C)`. -/
theorem renormalizedActivity_le_boundaryDecay
    (β entropy energy area entropyRate energyRate areaRate decayRate dΛ : ℝ)
    (hβ : 0 ≤ β)
    (hdΛ : 1 ≤ dΛ)
    (hEntropy : entropy ≤ entropyRate * area)
    (hEnergy : energyRate * area ≤ energy)
    (hArea : areaRate * Real.log dΛ ≤ area)
    (hNetGain : 0 ≤ β * energyRate - entropyRate)
    (hGain : decayRate ≤ areaRate * (β * energyRate - entropyRate)) :
    Real.exp (entropy - β * energy) ≤ Real.exp (-decayRate * Real.log dΛ) := by
  have hlog : 0 ≤ Real.log dΛ := Real.log_nonneg hdΛ
  have henergyMul : β * (energyRate * area) ≤ β * energy :=
    mul_le_mul_of_nonneg_left hEnergy hβ
  have hareaMul : (β * energyRate - entropyRate) *
      (areaRate * Real.log dΛ) ≤ (β * energyRate - entropyRate) * area :=
    mul_le_mul_of_nonneg_left hArea hNetGain
  have hgainMul : decayRate * Real.log dΛ ≤
      areaRate * (β * energyRate - entropyRate) * Real.log dΛ :=
    mul_le_mul_of_nonneg_right hGain hlog
  apply Real.exp_le_exp.mpr
  calc
    entropy - β * energy ≤ entropyRate * area - β * (energyRate * area) := by
      linarith
    _ = -(β * energyRate - entropyRate) * area := by ring
    _ ≤ -(β * energyRate - entropyRate) *
        (areaRate * Real.log dΛ) := by linarith
    _ ≤ -decayRate * Real.log dΛ := by
      nlinarith [hgainMul]

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
