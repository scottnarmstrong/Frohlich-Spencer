/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Complex.Basic
public import FroehlichSpencer.Surface.Site

/-! # Finite-difference Laplacian -/

public section

namespace FroehlichSpencer

/-- The printed finite-difference Laplacian, with off-diagonal sign `+1`. -/
@[expose] def latticeLaplacian (ν : ℕ) (f : Site ν → ℂ) (x : Site ν) : ℂ :=
  ∑ k : Fin ν,
    ((f (x + Pi.single k (1 : ℤ)) - f x) +
      (f (x - Pi.single k (1 : ℤ)) - f x))

end FroehlichSpencer


end
