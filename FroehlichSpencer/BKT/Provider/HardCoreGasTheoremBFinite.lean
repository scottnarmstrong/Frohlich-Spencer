/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation
public import FroehlichSpencer.BKT.Surface.HardCoreFracCorrelation
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.hardCoreGas_fracCorrelation_upper_bound`

This module contains `FroehlichSpencer.BKT.Provider.hardCoreGas_fracCorrelation_upper_bound`, the
proof of the statement `FroehlichSpencer.BKT.hardCoreGas_fracCorrelation_upper_bound` (file
`FroehlichSpencer/BKT/Surface/HardCoreGasTheoremBFinite.lean`, FS81 Theorem B for the hard-core gas
in finite volume, in FS81's activity range (5.27)).

The exponent is `β'(β) = c δ η² β` with `δ = 1/16 − max(ε, 0)`, `η = min(ξ, 1 − ξ)` and the
absolute `c` of the internal `coulombB_conditionLambda_free_fullRange_general`; the constant is
`A = 2 e^{β/(64δ)}`, uniform over the activity range `0 ≤ z ≤ K e^{εβ}` and the regions
(`Bridge.HardCoreFracCorrelation.finite_bound_activityRange`, through the bridge
`hardCoreFracCorrelation_eq_region` to the Condition-λ region correlation of the hard-core law).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap)

/-- **FS81 Theorem B, hard-core gas, finite volume, in the activity range (5.27)**: for every
`ξ ∈ (0, 1)` and `ε < 1/16` there is an exponent `β'(β) → ∞` such that for every `K` there is a
threshold `β₀` such that for every `β > β₀` one constant `A` serves every activity
`0 ≤ z ≤ K e^{εβ}`, every finite region
`Λ ∋ 0` and every `x ∈ Λ ∖ {0}`: `0 ≤ G_{ξ,Λ}(0, x) ≤ A |x|^{−β'(β)}`. -/
theorem hardCoreGas_fracCorrelation_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∀ ε : ℝ, ε < 1 / 16 →
      ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧ ∀ K : ℝ,
        ∃ β₀ : ℝ, ∀ β : ℝ, β₀ < β → ∃ A : ℝ,
        ∀ (z : ℝ) (hz : 0 ≤ z), z ≤ K * Real.exp (ε * β) →
        ∀ (Λ : Finset (ℤ × ℤ)) (h0 : (0 : ℤ × ℤ) ∈ Λ) (x : ℤ × ℤ) (hx : x ∈ Λ), x ≠ 0 →
          0 ≤ hardCoreFracCorrelation β z hz ξ Λ ⟨0, h0⟩ ⟨x, hx⟩ ∧
            hardCoreFracCorrelation β z hz ξ Λ ⟨0, h0⟩ ⟨x, hx⟩ ≤
              A * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-β' β) := by
  intro ξ hξ0 hξ1 ε hε
  obtain ⟨c, hc, hK⟩ := finite_bound_activityRange hξ0 hξ1 hε
  refine ⟨fun β => c * (1 / 16 - max ε 0) * dipoleGap ξ ^ 2 * β,
    tendsto_exponent_activityRange hc hξ0 hξ1 hε, fun K => ?_⟩
  obtain ⟨κ₀, -, hB⟩ := hK K
  exact ⟨κ₀, fun β hβ => ⟨2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * β), hB β hβ⟩⟩

end FroehlichSpencer.BKT.Provider

end
