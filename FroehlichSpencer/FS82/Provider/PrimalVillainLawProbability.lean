/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.PrimalInterface.PrimalBridge

/-! Provider of the gate `primalVillainLaw_isProbabilityMeasure` of the perimeter surface. -/

public section

namespace FroehlichSpencer.FS82.Provider

theorem primalVillainLaw_isProbabilityMeasure (R : Surface.RectBox4) (β : ℝ) (hβ : 0 < β) :
    MeasureTheory.IsProbabilityMeasure (Surface.primalVillainLaw R β hβ) :=
  PrimalInterface.primalVillainLaw_isProbabilityMeasure R β hβ

end FroehlichSpencer.FS82.Provider

end
