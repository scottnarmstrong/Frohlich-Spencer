/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceLatticeShift
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftBoxSet
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftBoxSetFinite
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftBox
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftUniform

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

noncomputable def sourceFiniteShiftAverage {α : Type*} [DecidableEq α]
    (n : ℕ) (f : SourceLatticeShift → PMF α) : PMF α :=
  PMF.bind (sourceShiftUniform n) f

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
