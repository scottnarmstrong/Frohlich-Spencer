/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FroehlichSpencer.BKT.Surface.ClockCorrelation

/-! # Long-range order of a harmonic of the `ℤ_n` clock two-point function -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The harmonic `ξ` of the infinite-volume `ℤ_n` clock two-point function has long-range order at
inverse temperature `β`: `⟨cos (ξ (θ_0 - θ_x))⟩^{(n)}(β)` does not tend to `0` as `|x| → ∞`; some
`ε > 0` bounds it from below at sites `x` of arbitrarily large Euclidean norm `|x|`. This is FS81's
"the `ℤ_n`-symmetry of the model is spontaneously broken" (§7.1, Remark 2, J p. 585) read at the
level of the free state's two-point function: the free state is `ℤ_n`-symmetric, and its
correlations stay away from `0` exactly when the symmetry is broken. -/
def IsClockLongRangeOrder (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ R : ℝ, ∃ x : ℤ × ℤ,
    R ≤ Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ∧ ε ≤ clockCorrelation n hn β hβ ξ 0 x

end FroehlichSpencer.BKT

end
