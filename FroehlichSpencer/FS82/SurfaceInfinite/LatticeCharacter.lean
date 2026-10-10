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
public import FroehlichSpencer.FS82.SurfaceInfinite.Torus4

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

def latticeCharacter (x : LatticePoint) (k : Torus4) : ℂ :=
  fourier (-x.1) k.1 * (fourier (-x.2.1) k.2.1 *
    (fourier (-x.2.2.1) k.2.2.1 * fourier (-x.2.2.2) k.2.2.2))

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
