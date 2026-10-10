/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import FroehlichSpencer.Surface.Site

/-! # Euclidean length on the lattice -/

public section

namespace FroehlichSpencer

/-- The Euclidean length of a lattice site, as in FS83. -/
@[expose] noncomputable def latticeLength (ν : ℕ) (x : Site ν) : ℝ :=
  Real.sqrt (∑ i : Fin ν, (x i : ℝ) ^ 2)

end FroehlichSpencer


end
