/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import FroehlichSpencer.BKT.Surface.CoulombPotential
public import FroehlichSpencer.BKT.Surface.HardCoreSecondMoment
import FroehlichSpencer.BKT.Provider.HardCoreGasTheoremAFinite

/-! # FS81 Theorem A for the hard-core gas, uniformly in the finite volume -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
FS81 Theorem A (J p. 532, (1.19)) for the hard-core gas, in the form derived
from Theorem 5.1 (J p. 564, (5.4) and the Remark (5.5)): for each `δ > 0` and `α` there is a
`β₀`, independent of `Λ`, such that for all `β > β₀` and `0 ≤ z ≤ e^{β/17 + α}`, every finite
region `Λ ⊂ ℤ²` and every real `g` supported in `Λ` with `∑_j g(j) = 0`,
`⟨φ(g)²⟩_Λ(β, z) ≥ (1 - δ) β ⟨g, -Δ⁻¹ g⟩`, with free boundary conditions and
`⟨g, -Δ⁻¹ g⟩ = ∑_{x, y} g(x) g(y) C(x - y)`, `C = coulombPotential`.
-/
theorem hardCoreGas_secondMoment_lower_bound :
    ∀ δ : ℝ, 0 < δ → ∀ α : ℝ, ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      ∀ (z : ℝ) (hz : 0 ≤ z), z ≤ Real.exp (β / 17 + α) →
        ∀ (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
          (hg : (g.sum fun _ a => a) = 0),
          (1 - δ) * β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) ≤
            hardCoreSecondMoment β hβ z hz Λ g hgΛ hg :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.hardCoreGas_secondMoment_lower_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
