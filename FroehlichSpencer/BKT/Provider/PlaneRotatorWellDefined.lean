/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.PlaneRotatorLaw
public import FroehlichSpencer.BKT.Surface.PlaneRotatorLaw
public import Mathlib.Probability.Notation
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.isProbabilityMeasure_planeRotatorLaw`

This module contains `FroehlichSpencer.BKT.Provider.isProbabilityMeasure_planeRotatorLaw`, the proof
of the statement `FroehlichSpencer.BKT.isProbabilityMeasure_planeRotatorLaw` (file
`FroehlichSpencer/BKT/Surface/PlaneRotatorWellDefined.lean`).

-/

@[expose] public section

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Rotator FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Bridge.PlaneRotatorLaw

noncomputable section

namespace FroehlichSpencer.BKT.Provider

theorem isProbabilityMeasure_planeRotatorLaw (β : ℝ) (Λ : Finset (ℤ × ℤ)) :
    IsProbabilityMeasure (planeRotatorLaw β Λ) := by
  rw [planeRotatorLaw_eq_freeRotatorMeasure]
  infer_instance

end FroehlichSpencer.BKT.Provider

end
