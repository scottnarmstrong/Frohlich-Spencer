/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.SurfaceZN.Box4
public import FroehlichSpencer.FS82.SurfaceZN.Cell4
public import FroehlichSpencer.FS82.SurfaceZN.coordIsEdge
public import FroehlichSpencer.FS82.SurfaceZN.cellAxes
public import FroehlichSpencer.FS82.SurfaceZN.cellDegree
public import FroehlichSpencer.FS82.SurfaceZN.Links
public import FroehlichSpencer.FS82.SurfaceZN.Config
public import FroehlichSpencer.FS82.SurfaceZN.linksFintype
public import FroehlichSpencer.FS82.SurfaceZN.positivePeriodFact
public import FroehlichSpencer.FS82.SurfaceZN.circleCosCharacter
public import FroehlichSpencer.FS82.SurfaceZN.pinningNormalizer
public import FroehlichSpencer.FS82.SurfaceZN.pinningNormalization
public import FroehlichSpencer.FS82.SurfaceZN.znPinningFactor

open scoped BigOperators
open MeasureTheory

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceZN

noncomputable section
open Classical

def znPinningDensity {B : Box4} (N : ℕ) (h : NNReal) (θ : Config B) : ℝ :=
  ∏ e : Links B, znPinningFactor N h (θ e)

end
end FroehlichSpencer.FS82.SurfaceZN

end
