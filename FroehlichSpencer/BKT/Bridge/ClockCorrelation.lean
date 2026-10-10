/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ClockCorrelationSpec
public import FroehlichSpencer.BKT.Bridge.ClockLaw

/-!
The net-limit correlation `clockCorrelation`  is the internal Ginibre free
limit `(clockModel n hn β hβ).twoPointLimit` (`clockCorrelation_eq`, from the characterization
`clockCorrelation_spec`).

With source's
`Bridge.PlaneRotatorCorrelation.planeRotatorCorrelation_eq_freeTwoPointLimit` and the internal
`Clock.correlation_dominates_rotator_limit` this proves the root
`planeRotatorCorrelation_le_clockCorrelation` (FS81 Theorem 7.1 (1); provider in `BKT/Provider/`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.ClockCorrelation

open FroehlichSpencer.BKT FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Bridge.ClockLaw

/-- The package's net-limit clock correlation is the internal Ginibre clock limit. -/
theorem clockCorrelation_eq (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) (j ℓ : ℤ × ℤ) :
    clockCorrelation n hn β hβ ξ j ℓ = (clockModel n hn β hβ).twoPointLimit ξ j ℓ :=
  ((clockCorrelation_spec n hn β hβ ξ j ℓ _).mp (tendsto_clockTwoPoint n hn β hβ ξ j ℓ)).symm

end FroehlichSpencer.BKT.Bridge.ClockCorrelation

end
