/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.SurfaceZN.positivePeriodFact
public import FroehlichSpencer.FS82.SurfaceZN.circleCosCharacter

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceZN

noncomputable section
open Classical

def pinningNormalizer (N : ℕ) (h : NNReal) : ℝ :=
  ∫ z : UnitAddCircle, Real.exp ((h : ℝ) * circleCosCharacter N z) ∂AddCircle.haarAddCircle

end
end FroehlichSpencer.FS82.SurfaceZN

end
