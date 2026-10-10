/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ConditionLambda
public import FroehlichSpencer.BKT.Surface.ConditionLambdaSecondMoment
import FroehlichSpencer.BKT.Provider.ConditionLambdaGasTheoremAFinite

/-! # FS81 Theorem A for lattice Coulomb gases satisfying Condition λ, finite volume -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/-- FS81 Theorem A (J p. 532, (1.19)) for the Coulomb gases satisfying Condition λ (J
p. 530) with constant `C` and parameters `α`, `ε` (so `ε < 1/16`), for a positive measure `dλ` (1.6)
with a vacancy `λ(0) ≥ ν > 0`, in the form derived from Theorem 5.1 (J p. 564,
(5.4) and the Remark (5.5)): for each `δ > 0` and all `C`, `α`, `ε` and `ν > 0` there is a `β₀` such
that for all `β > β₀` and every such `λ` the gas is summable and, for every finite region `Λ ⊂ ℤ²`
and every real `g` supported in `Λ` with `∑_j g(j) = 0`, `⟨φ(g)²⟩_Λ(β, λ) ≥ (1 - δ) β ⟨g, -Δ⁻¹ g⟩`,
with free boundary conditions and `⟨g, -Δ⁻¹ g⟩ = ∑_{x, y} g(x) g(y) C(x - y)`,
`C = coulombPotential`. The threshold depends on `δ`, `C`, `α`, `ε` and `ν`, not on `λ`, `Λ` or `g`. The positive vacancy assumption is implicit in the printed argument. -/
theorem conditionLambdaGas_secondMoment_lower_bound :
    ∀ δ : ℝ, 0 < δ → ∀ C α ε ν : ℝ, 0 < ν → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      ∀ lam : ℤ → ℝ, IsConditionLambda C α ε β lam →
      ∀ (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0), ν ≤ lam 0 →
      ∃ hS : IsCoulombGasSummable β lam,
      ∀ (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
        (hg : (g.sum fun _ a => a) = 0),
        (1 - δ) * β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) ≤
          conditionLambdaSecondMoment β hβ lam hlam hlam0 hS Λ g hgΛ hg :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.conditionLambdaGas_secondMoment_lower_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
