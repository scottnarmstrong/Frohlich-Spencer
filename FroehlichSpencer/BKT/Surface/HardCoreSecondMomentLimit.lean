/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Order.Filter.AtTopBot.Finset
public import FroehlichSpencer.BKT.Surface.HardCoreSecondMoment

/-! # Thermodynamic limits of the hard-core field second moments -/

open Filter Topology

@[expose] public section

namespace FroehlichSpencer.BKT

/-- `M` is a thermodynamic limit (FS81 J p. 530: "A thermodynamic limit `Λ ↑ ℤ²` can always be
constructed by a compactness argument") of the free-boundary hard-core field second moments
`⟨φ(g)²⟩_Λ(β, z)`: along some sequence of finite regions `Λ_k ↑ ℤ²` (eventually containing every
finite set), `⟨φ(g)²⟩_{Λ_k}(β, z) → M g` for every finitely supported neutral `g` (the terms
with `supp g ⊆ Λ_k`, which are all but finitely many). -/
def IsHardCoreSecondMomentLimit (β : ℝ) (hβ : 0 < β) (z : ℝ) (hz : 0 ≤ z)
    (M : (ℤ × ℤ →₀ ℝ) → ℝ) : Prop :=
  ∃ Λs : ℕ → Finset (ℤ × ℤ), Tendsto Λs atTop atTop ∧
    ∀ (g : ℤ × ℤ →₀ ℝ) (hg : (g.sum fun _ a => a) = 0),
      Tendsto (fun k : {k : ℕ // g.support ⊆ Λs k} =>
        hardCoreSecondMoment β hβ z hz (Λs k) g k.2 hg) atTop (𝓝 (M g))

end FroehlichSpencer.BKT

end
