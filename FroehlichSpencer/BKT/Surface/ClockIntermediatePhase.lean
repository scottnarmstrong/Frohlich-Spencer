/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FroehlichSpencer.BKT.Surface.ClockCorrelation

/-! # The massless intermediate phase of the `ℤ_n` clock model -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The `ℤ_n` clock model (`n ≥ 1`) is in the massless intermediate phase at inverse temperature
`β ≥ 0`, with harmonic margin `q` and lower scale `b` (FS81 §7.1, Remark 2, J p. 585: "Inequalities
(7.3) and (7.4) thus prove that … the inverse correlation length (mass gap), `m(β, n)`, of the
`ℤ_n`-model vanishes, i.e. there is a massless, intermediate phase"). The two clauses are FS81 (7.3)
and (7.4) for the free infinite-volume two-point function
`⟨cos (ξ (θ_0 - θ_x))⟩^{(n)}(β) = clockCorrelation n hn β hβ ξ 0 x` and the harmonics
`ξ = 1, …, n - 1` of Theorem 7.1, with `|·|` the Euclidean norm:
* (7.3), with `β' = b > 0`: every harmonic has the power-law lower bound
  `⟨e^{iξ(θ_0 - θ_x)}⟩^{(n)}(β) ≥ const (1 + |x|)^{-ξ²/(2πb)}` with a positive constant;
* (7.4): for some finite `β'' > 0`, every harmonic with `min(ξ/n, 1 - ξ/n) ≥ q` has the power-law
  upper bound `⟨e^{iξ(θ_0 - θ_x)}⟩^{(n)}(β) ≤ const (1 + |x|)^{-ξ²/(2πβ'')}`, one positive constant
  serving all of them.
The lower bound excludes exponential decay of every harmonic (vanishing mass gap); the upper bound
excludes long-range order of the restricted harmonics (unbroken `ℤ_n` symmetry). For the one-state
model `n = 1` the harmonic range is empty and the predicate holds for every `β`, `q` and `b > 0`;
the roots use it only for `n ≥ n₁`. -/
def IsClockIntermediatePhase (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (q b : ℝ) : Prop :=
  (0 < b ∧ ∀ ξ : ℤ, 1 ≤ ξ → ξ ≤ (n : ℤ) - 1 → ∃ A : ℝ, 0 < A ∧ ∀ x : ℤ × ℤ,
      A * (1 + Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2)) ^ (-((ξ : ℝ) ^ 2 / (2 * Real.pi * b))) ≤
        clockCorrelation n hn β hβ ξ 0 x) ∧
    ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, 0 < A ∧ ∀ ξ : ℤ, 1 ≤ ξ → ξ ≤ (n : ℤ) - 1 →
      q ≤ min ((ξ : ℝ) / n) (1 - (ξ : ℝ) / n) → ∀ x : ℤ × ℤ,
        clockCorrelation n hn β hβ ξ 0 x ≤
          A * (1 + Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2)) ^
            (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β'')))

end FroehlichSpencer.BKT

end
