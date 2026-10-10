/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ClockCorrelation
public import FroehlichSpencer.BKT.Bridge.PlaneRotatorCorrelation
public import FroehlichSpencer.BKT.Clock.CorrelationComparison
public import FroehlichSpencer.BKT.Surface.ClockCorrelation
public import FroehlichSpencer.BKT.Surface.PlaneRotatorCorrelation

/-!
# Provider for `FroehlichSpencer.BKT.planeRotatorCorrelation_le_clockCorrelation`

This module contains `FroehlichSpencer.BKT.Provider.planeRotatorCorrelation_le_clockCorrelation`, the
proof of the statement `FroehlichSpencer.BKT.planeRotatorCorrelation_le_clockCorrelation` (file
`FroehlichSpencer/BKT/Surface/ClockDominatesRotator.lean`, FS81 Theorem 7.1 (1)).

It is imported only
by that statement.

Both  correlations are free thermodynamic limits of the real cosine two-point functions
, so the comparison is the internal real-cosine comparison
`Clock.correlation_dominates_rotator_limit` at the sites `0, x`; it holds for every integer `ξ`, so
the range `1 ≤ ξ ≤ n - 1` is not used.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

theorem planeRotatorCorrelation_le_clockCorrelation (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β)
    (ξ : ℤ) (_hξ₁ : 1 ≤ ξ) (_hξ₂ : ξ ≤ (n : ℤ) - 1) (x : ℤ × ℤ) :
    planeRotatorCorrelation β hβ ξ 0 x ≤ clockCorrelation n hn β hβ ξ 0 x := by
  rw [Bridge.PlaneRotatorCorrelation.planeRotatorCorrelation_eq_freeTwoPointLimit,
    Bridge.ClockCorrelation.clockCorrelation_eq]
  exact Clock.correlation_dominates_rotator_limit n hn hβ ξ 0 x

end FroehlichSpencer.BKT.Provider

end
