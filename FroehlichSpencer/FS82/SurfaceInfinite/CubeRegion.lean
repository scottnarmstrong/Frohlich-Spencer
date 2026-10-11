/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import FroehlichSpencer.FS82.Surface.RectBox4

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

noncomputable def cubeRegion (N : ℕ) (hN : 0 < N) : RectBox4 where
  origin := fun _ => -(N : ℤ)
  side := fun _ => 2 * N
  side_pos := fun _ => Nat.mul_pos Nat.zero_lt_two hN

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
