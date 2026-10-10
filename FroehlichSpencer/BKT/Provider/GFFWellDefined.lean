/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.GFFMeasure
public import FroehlichSpencer.BKT.Surface.GFFLaw
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Provider for `FroehlichSpencer.BKT.isProbabilityMeasure_gffLaw`

This module contains `FroehlichSpencer.BKT.Provider.isProbabilityMeasure_gffLaw`, the proof of the
statement `FroehlichSpencer.BKT.isProbabilityMeasure_gffLaw` (file
`FroehlichSpencer/BKT/Surface/GFFWellDefined.lean`).

-/

@[expose] public section

namespace FroehlichSpencer.BKT.Provider

open MeasureTheory
open Multigraph

universe u v

/--
The Gaussian free field law of KP (1.3) is normalized: it is the internal rooted law
`gffMeasure`, whose partition function is finite and positive on a connected graph.
-/
theorem isProbabilityMeasure_gffLaw {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β) (v : V) :
    IsProbabilityMeasure (gffLaw G hG β hβ v) := by
  classical
  rw [gffLaw_eq_gffMeasure G hG β hβ v]
  exact gffMeasure_isProbabilityMeasure G hG β hβ v

end FroehlichSpencer.BKT.Provider

end
