/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import FroehlichSpencer.BKT.Surface.CoulombPotential
public import FroehlichSpencer.BKT.Surface.HardCoreSecondMomentLimit
import FroehlichSpencer.BKT.Provider.HardCoreGasTheoremA

/-! # FS81 Theorem A for the hard-core gas in infinite volume -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
FS81 Theorem A (J p. 532, (1.19)) for the hard-core gas (Theorem 5.1's class,
J pp. 563–564) in infinite volume: for each `δ > 0` and `α` there is a `β₀` such that for all
`β > β₀` and `0 ≤ z ≤ e^{β/17 + α}`, a thermodynamic limit of the free-boundary field second
moments exists, and in every thermodynamic limit
`⟨φ(g)²⟩ ≥ (1 - δ) β ⟨g, -Δ⁻¹ g⟩` whenever `∑_j g(j) = 0`, with
`⟨g, -Δ⁻¹ g⟩ = ∑_{x, y} g(x) g(y) C(x - y)`, `C = coulombPotential`.
-/
theorem hardCoreGas_secondMomentLimit_lower_bound :
    ∀ δ : ℝ, 0 < δ → ∀ α : ℝ, ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      ∀ (z : ℝ) (hz : 0 ≤ z), z ≤ Real.exp (β / 17 + α) →
        (∃ M : (ℤ × ℤ →₀ ℝ) → ℝ, IsHardCoreSecondMomentLimit β hβ z hz M) ∧
        ∀ M : (ℤ × ℤ →₀ ℝ) → ℝ, IsHardCoreSecondMomentLimit β hβ z hz M →
          ∀ g : ℤ × ℤ →₀ ℝ, (g.sum fun _ a => a) = 0 →
            (1 - δ) * β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) ≤
              M g :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.hardCoreGas_secondMomentLimit_lower_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
