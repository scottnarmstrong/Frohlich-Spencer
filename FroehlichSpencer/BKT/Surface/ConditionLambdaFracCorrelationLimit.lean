/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic
public import FroehlichSpencer.BKT.Surface.ConditionLambdaFracCorrelation

/-! # Thermodynamic limits of the fractional-charge correlations of a lattice Coulomb gas -/

open Filter Topology

@[expose] public section

namespace FroehlichSpencer.BKT

/-- `G` is a thermodynamic limit (FS81 J p. 530: "A thermodynamic limit `Λ ↑ ℤ²` can always be
constructed by a compactness argument") of the free-boundary fractional-charge correlations
`G_{ξ,Λ}(0, x)` (1.23) of the Coulomb gas with a priori weights `λ`: along some sequence of finite
regions `Λ_k ↑ ℤ²` (eventually containing every finite set), `G_{ξ,Λ_k}(0, x) → G(x)` for every
`x ∈ ℤ²` (the terms with `0, x ∈ Λ_k`, which are all but finitely many). -/
def IsConditionLambdaFracCorrelationLimit (β : ℝ) (lam : ℤ → ℝ) (hlam : ∀ q, 0 ≤ lam q)
    (hlam0 : 0 < lam 0) (hS : IsCoulombGasSummable β lam) (ξ : ℝ) (G : ℤ × ℤ → ℝ) : Prop :=
  ∃ Λs : ℕ → Finset (ℤ × ℤ), Tendsto Λs atTop atTop ∧
    ∀ x : ℤ × ℤ, Tendsto (fun k : {k : ℕ // (0 : ℤ × ℤ) ∈ Λs k ∧ x ∈ Λs k} =>
      conditionLambdaFracCorrelation β lam hlam hlam0 hS ξ (Λs k) ⟨0, k.2.1⟩ ⟨x, k.2.2⟩) atTop
      (𝓝 (G x))

end FroehlichSpencer.BKT

end
