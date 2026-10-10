/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import FroehlichSpencer.FS82.SurfaceInfinite.LatticePoint

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

def AbsolutelySummableCorrelation (C : LatticePoint → ℝ) : Prop :=
  Summable fun d => |C d|

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
