/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Analysis.Complex.Trigonometric
public import FroehlichSpencer.FS82.Currents.BranchEnvelope
public import FroehlichSpencer.FS82.Gaussian.SourceDualComplex

public import FroehlichSpencer.FS82.Currents.Expansion
public import FroehlichSpencer.FS82.Gaussian.LatticePath

/-!
# Integer currents and the decay exponent

The activity envelope and Gaussian coercivity estimate combine to give
(2.103) with the corrected positive rate `a(β)=(β/216-β₁)/2`.
-/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Moment.CurrentDecay

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open Classical

noncomputable section

/--
Repackage a lineage's finite function as the shared integer current.
-/
def integerCurrentOfFunction {B : Box 4} (j : Link B → ℤ) :
    IntegerCurrent B :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ (Link B)).symm j

@[simp] theorem integerCurrentOfFunction_apply {B : Box 4}
    (j : Link B → ℤ) (e : Link B) : integerCurrentOfFunction j e = j e := by
  simp [integerCurrentOfFunction]


end
end FroehlichSpencer.FS82.Moment.CurrentDecay
