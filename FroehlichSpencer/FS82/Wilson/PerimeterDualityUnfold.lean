/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.DualityInteger
import all FroehlichSpencer.FS82.Wilson.DualityInteger

/-!
`Wilson/DualityInteger.lean` does not expose `dualIntegerHomogeneousSupport`,
`sourceDualGaugeClassPartition`, `sourceDualGaugeClassTiltSum` and
`sourceDiscreteDualExpectation` outside its module.

The chord bridge needs their definitions.

This
module imports the private scope of that file and states them as an `Iff` and an equation.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Gaussian

/-- The definition of homogeneous support of an integer dual chain. -/
theorem dualIntegerHomogeneousSupport_iff {B : SourceBox} (q : DualIntegerChain B) (k : ℕ) :
    dualIntegerHomogeneousSupport q k ↔ ∀ c ∈ q.support, Cubical.dualCellDegree c = k :=
  Iff.rfl

/-- The definition of the discrete dual expectation as a ratio of sums over the exact integer dual
two-fields. -/
theorem sourceDiscreteDualExpectation_eq_tsum_div {B : SourceBox} (β : ℝ)
    (sigma : DualIntegerChain B) :
    sourceDiscreteDualExpectation β sigma =
      (∑' x : SourceIntegerDualGaugeClass B,
          sourceDualGaugeClassWeight β x * sourceDualGaugeClassObservable β sigma x) /
        ∑' x : SourceIntegerDualGaugeClass B, sourceDualGaugeClassWeight β x := by
  unfold sourceDiscreteDualExpectation sourceDualGaugeClassTiltSum sourceDualGaugeClassPartition
  rfl

end FroehlichSpencer.FS82.Wilson

end
