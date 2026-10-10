/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic
public import FroehlichSpencer.BKT.Surface.ConditionLambdaSecondMoment

/-! # Thermodynamic limits of the field second moments of a lattice Coulomb gas -/

open Filter Topology

@[expose] public section

namespace FroehlichSpencer.BKT

/-- `M` is a thermodynamic limit (FS81 J p. 530: "A thermodynamic limit `Λ ↑ ℤ²` can always be
constructed by a compactness argument") of the free-boundary field second moments `⟨φ(g)²⟩_Λ(β, λ)`
of the Coulomb gas with a priori weights `λ`: along some sequence of finite regions `Λ_k ↑ ℤ²`
(eventually containing every finite set), `⟨φ(g)²⟩_{Λ_k}(β, λ) → M g` for every finitely supported
neutral `g` (the terms with `supp g ⊆ Λ_k`, which are all but finitely many). -/
def IsConditionLambdaSecondMomentLimit (β : ℝ) (hβ : 0 < β) (lam : ℤ → ℝ) (hlam : ∀ q, 0 ≤ lam q)
    (hlam0 : 0 < lam 0) (hS : IsCoulombGasSummable β lam) (M : (ℤ × ℤ →₀ ℝ) → ℝ) : Prop :=
  ∃ Λs : ℕ → Finset (ℤ × ℤ), Tendsto Λs atTop atTop ∧
    ∀ (g : ℤ × ℤ →₀ ℝ) (hg : (g.sum fun _ a => a) = 0),
      Tendsto (fun k : {k : ℕ // g.support ⊆ Λs k} =>
        conditionLambdaSecondMoment β hβ lam hlam hlam0 hS (Λs k) g k.2 hg) atTop (𝓝 (M g))

end FroehlichSpencer.BKT

end
