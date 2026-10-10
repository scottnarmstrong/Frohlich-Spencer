/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FroehlichSpencer.BKT.Surface.ConditionLambda
public import FroehlichSpencer.BKT.Surface.ConditionLambdaFracCorrelation
import FroehlichSpencer.BKT.Provider.ConditionLambdaGasTheoremBFinite

/-! # FS81 Theorem B for lattice Coulomb gases satisfying Condition λ, finite volume -/

open Filter

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/-- FS81 Theorem B (J p. 533, (1.25)) for the Coulomb gases satisfying Condition λ (J
p. 530) with constant `C` and parameters `α`, `ε` (so `ε < 1/16`), for a positive measure `dλ` (1.6)
with a vacancy `λ(0) ≥ ν > 0`, in finite volume with free boundary conditions: for
each `0 < ξ < 1` and `ε` there is an exponent `β' = β'(β, ξ)` with `β' → ∞` as `β → ∞`, and for all
`C`, `α`, `ν > 0` and all sufficiently large `β` there is a constant such that for every such `λ`
the gas is summable and `0 ≤ G_{ξ,Λ}(0, x) ≤ const |x|^{-β'}` for every finite region `Λ ∋ 0` and
every `x ∈ Λ ∖ {0}`, with `G_{ξ,Λ}` the fractional-charge correlation (1.23) and `|·|` the Euclidean
norm. The exponent depends on `ξ` and `ε`, the threshold on `ξ`, `ε`, `C`, `α` and `ν`; the constant
may depend on these and on `β`, not on `λ`, `Λ` or `x`. The positive vacancy assumption is implicit in the printed argument. -/
theorem conditionLambdaGas_fracCorrelation_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∀ ε : ℝ, ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ C α ν : ℝ, 0 < ν → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ < β → ∃ A : ℝ,
        ∀ lam : ℤ → ℝ, IsConditionLambda C α ε β lam →
        ∀ (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0), ν ≤ lam 0 →
        ∃ hS : IsCoulombGasSummable β lam,
        ∀ (Λ : Finset (ℤ × ℤ)) (h0 : (0 : ℤ × ℤ) ∈ Λ) (x : ℤ × ℤ) (hx : x ∈ Λ), x ≠ 0 →
          0 ≤ conditionLambdaFracCorrelation β lam hlam hlam0 hS ξ Λ ⟨0, h0⟩ ⟨x, hx⟩ ∧
            conditionLambdaFracCorrelation β lam hlam hlam0 hS ξ Λ ⟨0, h0⟩ ⟨x, hx⟩ ≤
              A * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-β' β) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.conditionLambdaGas_fracCorrelation_upper_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
