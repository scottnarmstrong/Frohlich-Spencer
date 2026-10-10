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
import FroehlichSpencer.BKT.Provider.VillainPowerLaw

/-! # KP Theorem 1.3: power-law lower bound for the Villain model -/

open MeasureTheory

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
Kharash–Peled Theorem 1.3 (p. 4).

There are `β₀, C > 0` such that for every
`L > 1`, every `β > β₀` and every vertex `j` of `Λ_L^zero`,
`E^Vil_{β,Λ_L^zero}[cos θ_j] ≥ (dist (j, z) + 1) ^ (-C / β)`; the wired vertex `z` is `none`.
-/
theorem villain_powerLaw_lower_bound :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 < C ∧
      ∀ L : ℕ, 1 < L → ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
        ∀ j : Option (Fin L × Fin L),
          ((squareZero L).toSimpleGraph.dist j none + 1 : ℝ) ^ (-C / β) ≤
            ∫ θ, Real.cos (θ j) ∂(villainLaw L β hβ) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.villain_powerLaw_lower_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
