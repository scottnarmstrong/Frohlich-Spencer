/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # The `(Γ, η, θ)`-sub-Gaussian condition (KP Definition 1.4) -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- KP Definition 1.4 (p. 5) at inverse temperature `β`: `lam` is a real, even, normalized
trigonometric polynomial (KP p. 4), `lam φ = 1 + 2 ∑_{q=1}^N lamHat q · cos (q φ)` for some
integer `N > 0` and real coefficients, with `lamHat q = 0` for `q > N`, and (1.9)
`|lamHat q| ≤ Γ · exp ((η + θ / β) q²)` for `q ≥ 1`. -/
def IsSubGaussian (Γ η θ β : ℝ) (lam : ℝ → ℝ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∃ lamHat : ℕ → ℝ, (∀ q : ℕ, N < q → lamHat q = 0) ∧
    (∀ φ : ℝ, lam φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 N, lamHat q * Real.cos (q * φ)) ∧
    ∀ q : ℕ, 1 ≤ q → |lamHat q| ≤ Γ * Real.exp ((η + θ / β) * q ^ 2)

end FroehlichSpencer.BKT

end
