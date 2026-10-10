/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FroehlichSpencer.BKT.Surface.ClockCorrelation

/-! # Exponential decay of a harmonic of the `ℤ_n` clock two-point function -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The harmonic `ξ` of the infinite-volume `ℤ_n` clock two-point function decays exponentially
at inverse temperature `β` (FS81 §7.1: "connected correlations have exponential fall-off", J p. 589;
a positive mass gap, the inverse correlation length `m(β, n)` of J p. 585): for some `C` and
`m > 0`, `⟨cos (ξ (θ_0 - θ_x))⟩^{(n)}(β) ≤ C e^{-m |x|}` for every site `x`, `|·|` the Euclidean
norm. The correlation is nonnegative (Ginibre's inequality), so this one-sided bound is the decay
of its absolute value. -/
def IsClockExpDecay (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) : Prop :=
  ∃ C m : ℝ, 0 < m ∧ ∀ x : ℤ × ℤ,
    clockCorrelation n hn β hβ ξ 0 x ≤
      C * Real.exp (-m * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2))

end FroehlichSpencer.BKT

end
