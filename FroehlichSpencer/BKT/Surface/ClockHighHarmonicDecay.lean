/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Basic
public import FroehlichSpencer.BKT.Surface.ClockCorrelation
import FroehlichSpencer.BKT.Provider.ClockHighHarmonicDecay

/-! # FS81 Theorem 7.1 (2): decay of the high harmonics of the `ℤ_n` clock model -/

open Filter Topology

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
FS81 Theorem 7.1 (2) (J p. 585).

Given `β` and `q ∈ (0, 1)`, there exists some
`n₀ = n₀(β, q) < ∞` such that for all `n ≥ n₀` and all `ξ = 1, …, n - 1` with
`min(ξ/n, 1 - ξ/n) ≥ q`, `⟨e^{iξ(θ_0 - θ_x)}⟩^{(n)}(β) ≤ const (1 + |x|)^{-ξ²/(2πβ'')}` for some
`β'' = β''(β, n, q) < ∞`.

Moreover, `n₀(β, q) → ∞` when `β → ∞` or `q → 0`.

Here the two-point
function is the free thermodynamic limit `clockCorrelation n hn β hβ ξ 0 x`, the real form
`⟨cos (ξ (θ_0 - θ_x))⟩^{(n)}(β)`; `|·|` is the Euclidean norm; one `β''` and one constant serve
every allowed `ξ`; the constant is positive.
-/
theorem clockCorrelation_highHarmonic_upper_bound :
    ∃ n₀ : ℝ → ℝ → ℕ, (∀ q : ℝ, 0 < q → q < 1 → Tendsto (fun β => n₀ β q) atTop atTop) ∧
      (∀ β : ℝ, 0 ≤ β → Tendsto (fun q => n₀ β q) (𝓝[>] 0) atTop) ∧
      ∀ (β : ℝ) (hβ : 0 ≤ β) (q : ℝ), 0 < q → q < 1 → ∀ (n : ℕ) (hn : 0 < n), n₀ β q ≤ n →
        ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, 0 < A ∧ ∀ ξ : ℤ, 1 ≤ ξ → ξ ≤ (n : ℤ) - 1 →
          q ≤ min ((ξ : ℝ) / n) (1 - (ξ : ℝ) / n) → ∀ x : ℤ × ℤ,
            clockCorrelation n hn β hβ ξ 0 x ≤
              A * (1 + Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2)) ^
                (-((ξ : ℝ) ^ 2 / (2 * Real.pi * β''))) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.clockCorrelation_highHarmonic_upper_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
