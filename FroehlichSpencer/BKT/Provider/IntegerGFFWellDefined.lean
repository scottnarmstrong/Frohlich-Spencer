/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.IntegerGFFMeasure
public import FroehlichSpencer.BKT.Surface.IntegerGFFLaw
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Provider for `FroehlichSpencer.BKT.isProbabilityMeasure_integerGFFLaw`

This module will contain `FroehlichSpencer.BKT.Provider.isProbabilityMeasure_integerGFFLaw`, the proof of the
statement `FroehlichSpencer.BKT.isProbabilityMeasure_integerGFFLaw` (file `FroehlichSpencer/BKT/Surface/IntegerGFFWellDefined.lean`).

-/

@[expose] public section

namespace FroehlichSpencer.BKT.Provider

open MeasureTheory
open Multigraph

universe u v

/--
The rooted integer Gaussian free field law is normalized, by identifying its total
mass with KP's positive summable lattice partition function.
-/
theorem isProbabilityMeasure_integerGFFLaw {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (β : ℝ) (hβ : 0 < β)
    (v : V) :
    IsProbabilityMeasure (integerGFFLaw G hG β hβ v) := by
  classical
  rw [isProbabilityMeasure_iff]
  dsimp [integerGFFLaw]
  rw [integerGFFDensityMeasure_univ G hG β hβ v]
  apply ENNReal.inv_mul_cancel
  · exact ENNReal.ofReal_ne_zero_iff.mpr
      (igffPartitionFunction_pos G hG β hβ v)
  · exact ENNReal.ofReal_ne_top

end FroehlichSpencer.BKT.Provider

end
