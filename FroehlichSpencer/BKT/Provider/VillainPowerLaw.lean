/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FroehlichSpencer.BKT.Surface.MultigraphSimpleGraph
public import FroehlichSpencer.BKT.Surface.SquareZero
public import FroehlichSpencer.BKT.Surface.VillainLaw
import FroehlichSpencer.BKT.Reduction.T62ImpliesT13
import FroehlichSpencer.BKT.Surface.WeightedGFFRenormalization

/-!
# Provider for `FroehlichSpencer.BKT.villain_powerLaw_lower_bound`

This module contains `FroehlichSpencer.BKT.Provider.villain_powerLaw_lower_bound`, the proof of the
statement `FroehlichSpencer.BKT.villain_powerLaw_lower_bound` (file
`FroehlichSpencer/BKT/Surface/VillainPowerLaw.lean`).

KP Theorem 1.3 from the KP Theorem 1.6 (`Reduction.t13_of_t16Statement_final`, KP §6).
-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.BKT.Provider

/--
KP Theorem 1.3 from the KP Theorem 1.6 (`Reduction.t13_of_t16Statement_final`, KP §6).
-/
theorem villain_powerLaw_lower_bound :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 < C ∧
      ∀ L : ℕ, 1 < L → ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
        ∀ j : Option (Fin L × Fin L),
          ((squareZero L).toSimpleGraph.dist j none + 1 : ℝ) ^ (-C / β) ≤
            ∫ θ, Real.cos (θ j) ∂(villainLaw L β hβ) :=
  Reduction.t13_of_t16Statement_final FroehlichSpencer.BKT.weightedGFF_renormalization

end FroehlichSpencer.BKT.Provider

end
