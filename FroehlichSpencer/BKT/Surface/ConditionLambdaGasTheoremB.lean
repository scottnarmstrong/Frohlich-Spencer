/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FroehlichSpencer.BKT.Surface.ConditionLambda
public import FroehlichSpencer.BKT.Surface.ConditionLambdaFracCorrelationLimit
import FroehlichSpencer.BKT.Provider.ConditionLambdaGasTheoremB

/-! # FS81 Theorem B for lattice Coulomb gases satisfying Condition λ, infinite volume -/

open Filter

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/-- FS81 Theorem B (J p. 533, (1.25)) for the Coulomb gases satisfying Condition λ (J
p. 530) with constant `C` and parameters `α`, `ε` (so `ε < 1/16`), for a positive measure `dλ` (1.6)
with a vacancy `λ(0) ≥ ν > 0`, in infinite volume: for each `0 < ξ < 1` and `ε`
there is an exponent `β' = β'(β, ξ)` with `β' → ∞` as `β → ∞`, and for all `C`, `α`, `ν > 0` and all
sufficiently large `β` there is a constant such that for every such `λ` the gas is summable, a
thermodynamic limit `G_ξ` of the free-boundary fractional-charge correlations (1.23) exists, and
every thermodynamic limit satisfies `0 ≤ G_ξ(x) ≤ const |x|^{-β'}` for every `x ≠ 0`. Here `|·|` is
the Euclidean norm; the exponent depends on `ξ` and `ε`, the threshold on `ξ`, `ε`, `C`, `α` and
`ν`; the constant may depend on these and on `β`, not on `λ`, `x` or the limit. The positive vacancy assumption is implicit in the printed argument. -/
theorem conditionLambdaGas_fracCorrelationLimit_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∀ ε : ℝ, ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ C α ν : ℝ, 0 < ν → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ < β → ∃ A : ℝ,
        ∀ lam : ℤ → ℝ, IsConditionLambda C α ε β lam →
        ∀ (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0), ν ≤ lam 0 →
        ∃ hS : IsCoulombGasSummable β lam,
          (∃ G : ℤ × ℤ → ℝ, IsConditionLambdaFracCorrelationLimit β lam hlam hlam0 hS ξ G) ∧
          ∀ G : ℤ × ℤ → ℝ, IsConditionLambdaFracCorrelationLimit β lam hlam hlam0 hS ξ G →
            ∀ x : ℤ × ℤ, x ≠ 0 →
              0 ≤ G x ∧ G x ≤ A * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-β' β) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.conditionLambdaGas_fracCorrelationLimit_upper_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
