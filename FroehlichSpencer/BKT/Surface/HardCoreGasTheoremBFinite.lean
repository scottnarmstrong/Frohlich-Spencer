/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import FroehlichSpencer.BKT.Surface.HardCoreFracCorrelation
import FroehlichSpencer.BKT.Provider.HardCoreGasTheoremBFinite

/-! # FS81 Theorem B for the hard-core gas, uniformly in the finite volume -/

open Filter

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
FS81 Theorem B (J p. 533, (1.25)) for the hard-core gas, in the activity range of
FS81's statement (5.27) for it (J p. 568: "provided `ξ ∈ (0, 1)` and `z ≤ const e^{εβ}`, with
`ε < 1/16`"), with `G_ξ` given by (1.23) on a finite region with free boundary conditions: for each
`0 < ξ < 1` and `ε < 1/16` there is an exponent `β' = β'(β, ξ)` with `β' → ∞` as `β → ∞` such that
for every constant `K` and all sufficiently large `β`, `0 ≤ G_{ξ,Λ}(0, x) ≤ const |x|^{-β'}` for
every activity `0 ≤ z ≤ K e^{εβ}`, every finite `Λ ⊂ ℤ²` containing `0` and every `x ≠ 0`.

Here
`|·|` is the Euclidean norm; the exponent depends on `ξ` and `ε`, the threshold on `ξ`, `ε` and
`K`; the constant may depend on `ξ`, `ε`, `K` and `β`, not on `z`, `Λ` or `x`.
-/
theorem hardCoreGas_fracCorrelation_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∀ ε : ℝ, ε < 1 / 16 →
      ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧ ∀ K : ℝ,
        ∃ β₀ : ℝ, ∀ β : ℝ, β₀ < β → ∃ A : ℝ,
        ∀ (z : ℝ) (hz : 0 ≤ z), z ≤ K * Real.exp (ε * β) →
        ∀ (Λ : Finset (ℤ × ℤ)) (h0 : (0 : ℤ × ℤ) ∈ Λ) (x : ℤ × ℤ) (hx : x ∈ Λ), x ≠ 0 →
          0 ≤ hardCoreFracCorrelation β z hz ξ Λ ⟨0, h0⟩ ⟨x, hx⟩ ∧
            hardCoreFracCorrelation β z hz ξ Λ ⟨0, h0⟩ ⟨x, hx⟩ ≤
              A * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-β' β) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.hardCoreGas_fracCorrelation_upper_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
