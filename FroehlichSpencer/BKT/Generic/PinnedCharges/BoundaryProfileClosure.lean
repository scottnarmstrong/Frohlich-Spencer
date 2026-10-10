/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.PinnedEnergyProfiles
public import FroehlichSpencer.BKT.Generic.PinnedCharges.PinnedActivityRate

/-! # Conditional pinned profile-to-activity closure

This module joins the pinned variational estimate to the Appendix D activity
arithmetic with the constants from the tent-profile calculation. It leaves the
selection geometry, profile incidence, boundary entropy count, and cover-growth
estimate as explicit hypotheses.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator

variable {L : ℕ}

/-- The pinned Dirichlet Green energy of a finite-box charge. -/
def pinnedGreenEnergy (hL : 1 < L) (q : Site L → ℤ) : ℝ :=
  Multigraph.pairing (realNeutralizeAtWiredRoot q)
    (-(squareZero L).greenOp (squareZero_connected L hL)
      (realNeutralizeAtWiredRoot q))

/-- The multiscale profile bounds `|⟨U,q⟩| ≥ (A₀+P)/2` and
`E_D(U) ≤ 54(A₀+P)` imply the pinned Green-energy lower bound with the
constant `1/216`. -/
theorem pinnedGreenEnergy_ge_of_multiscaleProfiles (hL : 1 < L)
    (q : Site L → ℤ) (U : RotatorDualFace L → ℝ) (hUroot : U none = 0)
    (A₀ P : ℝ) (hA₀ : 0 ≤ A₀) (hP : 0 ≤ P)
    (hpair : (A₀ + P) / 2 ≤ |∑ x, U (some x) * (q x : ℝ)|)
    (hprofileEnergy : (squareZero L).energy U ≤ 54 * (A₀ + P)) :
    (A₀ + P) / 216 ≤ pinnedGreenEnergy hL q := by
  have harea : 0 ≤ A₀ + P := add_nonneg hA₀ hP
  have hbase := pinned_greenEnergy_ge_of_profile hL q U hUroot
    ((A₀ + P) / 2) 108 (by positivity) (by norm_num)
    hpair (by nlinarith [hprofileEnergy])
  dsimp [pinnedGreenEnergy]
  nlinarith

/-- Once the profile calculation supplies `area/216 ≤ E_D(q)`, the boundary
entropy and cover-growth bounds imply every prescribed activity power at the
explicit low-temperature threshold. -/
theorem pinnedActivity_le_any_power_of_multiscaleProfiles
    (hL : 1 < L) (q : Site L → ℤ) (U : RotatorDualFace L → ℝ)
    (hUroot : U none = 0) (A₀ P entropy entropyRate areaRate R dΛ β : ℝ)
    (hA₀ : 0 ≤ A₀) (hP : 0 ≤ P)
    (hpair : (A₀ + P) / 2 ≤ |∑ x, U (some x) * (q x : ℝ)|)
    (hprofileEnergy : (squareZero L).energy U ≤ 54 * (A₀ + P))
    (hEntropy : entropy ≤ entropyRate * (A₀ + P))
    (hArea : areaRate * Real.log dΛ ≤ A₀ + P)
    (hβ : 0 ≤ β) (hdΛ : 1 ≤ dΛ) (hR : 0 ≤ R)
    (hAreaRate : 0 < areaRate)
    (hThreshold : (R / areaRate + entropyRate) / (1 / 216 : ℝ) ≤ β) :
    Real.exp (entropy - β * pinnedGreenEnergy hL q) ≤
      Real.exp (-R * Real.log dΛ) := by
  have henergy := pinnedGreenEnergy_ge_of_multiscaleProfiles hL q U hUroot
    A₀ P hA₀ hP hpair hprofileEnergy
  have hArea0 : 0 ≤ A₀ + P := add_nonneg hA₀ hP
  have hEnergy : (1 / 216 : ℝ) * (A₀ + P) ≤ pinnedGreenEnergy hL q := by
    nlinarith [henergy]
  exact renormalizedActivity_le_any_boundary_power β entropy
    (pinnedGreenEnergy hL q) (A₀ + P) entropyRate (1 / 216 : ℝ)
    areaRate R dΛ hβ hdΛ hEntropy hEnergy hArea hR (by norm_num) hAreaRate
    hThreshold

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
