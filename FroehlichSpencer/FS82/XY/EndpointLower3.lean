/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Endpoint3
public import FroehlichSpencer.FS82.XY.Activity3

/-!
# the endpoint character from below above the activity threshold

`exp(−‖ε‖²/(2β) − E) ≤ Re ⟨e^{i(θ_x − θ_y)}⟩`

whenever on every terminal branch the translated phases have representatives modulo `2π` with
Jensen budget at most `E`.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.XY.GaugeAverage

variable {B : Dual3Box}

/-- **The endpoint character from below above the activity threshold.** -/
theorem xy3_endpointExpectation_lower_of_phaseRepresentatives_of_threshold {β : ℝ}
    (hβ : 400 / 3 < β) (x y : XYSites B) (E : ℝ)
    (hE : ∀ ω : XY3Branch B, ∃ θ' : XY3BranchIndex ω → ℝ,
      (∀ i, xy3BranchAmp β ω i ≠ 0 → ∃ n : ℤ,
        linkPairing (xy3PathShift β x y) (xy3BranchCurrent ω i) + θ' i =
          2 * Real.pi * (n : ℝ)) ∧
      ∑ i, SourceJensen.sourceJensenGamma (xy3BranchAmp β ω i) * θ' i ^ 2 ≤ E) :
    Real.exp (-(xyDual3ResidualEnergy x y / (2 * β)) - E) ≤
      (xyEndpointCharacterExpectation β x y).re :=
  xy3_endpointExpectation_lower_of_phaseRepresentatives (by linarith) x y E
    (xy3BranchAmp_lt_one hβ) hE

end FroehlichSpencer.FS82.XY

end
