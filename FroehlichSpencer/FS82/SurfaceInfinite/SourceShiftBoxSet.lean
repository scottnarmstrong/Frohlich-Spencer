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

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

noncomputable def sourceShiftBoxSet (n : ℕ) : Set SourceLatticeShift :=
  {a | ∀ i, a i ∈ Set.Icc (-(n : ℤ)) (n : ℤ)}

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
