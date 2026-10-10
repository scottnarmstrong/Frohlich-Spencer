/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.SOSLiteral
public import FroehlichSpencer.BKT.Surface.SOSLiteralLimit
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.isProbabilityMeasure_sosLiteralDiffLaw`

-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open FroehlichSpencer.BKT FroehlichSpencer.BKT.SOS.Literal
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site)
open FroehlichSpencer.BKT.SOS.Roughening (pinnedGrad pinnedField)
open FroehlichSpencer.BKT.Bridge.SOSLiteral

/-- **The gate.** -/
theorem isProbabilityMeasure_sosLiteralDiffLaw (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (ℤ × ℤ)) (w : ℤ × ℤ) (hw : w ∈ A) (R : ℕ)
    (hA : A ⊆ Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R) :
    IsProbabilityMeasure (sosLiteralDiffLaw β hβ hβ1 A w hw R hA) := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · exact isProbabilityMeasure_zero hβ hβ1 hw hA
  · rw [sosLiteralDiffLaw_eq_diffLaw hβ hβ1 hw R hA]
    exact isProbabilityMeasure_diffLaw hβ hβ1 A w (by omega)

end FroehlichSpencer.BKT.Provider

end
