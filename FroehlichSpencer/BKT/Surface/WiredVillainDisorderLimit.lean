/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import FroehlichSpencer.BKT.Surface.VillainLaw
public import FroehlichSpencer.BKT.Surface.WiredVillainDisorder

/-! # Thermodynamic limits of the wired-box Villain disorder expectations -/

open MeasureTheory Filter Topology

@[expose] public section

namespace FroehlichSpencer.BKT

/-- `D` is a thermodynamic limit of the disorder expectations `⟨D^ξ_{0x}⟩(β)`, `x = (n, 0)`, of the
Villain model along the wired boxes `Λ_L^zero` with `0` at the centre `(⌊L/2⌋, ⌊L/2⌋)`: along some
sequence of sides `L_k → ∞`, the expectation in `Λ_{L_k}^zero` of `D^ξ_{0x}` converges to `D n`, for
every `n` (the terms whose string lies in the box, which are all but finitely many). -/
def IsWiredVillainDisorderLimit (β : ℝ) (hβ : 0 < β) (ξ : ℝ) (D : ℕ → ℝ) : Prop :=
  ∃ Ls : ℕ → ℕ, Tendsto Ls atTop atTop ∧ ∀ n : ℕ,
    Tendsto (fun k : {k : ℕ // Ls k / 2 + n < Ls k ∧ Ls k / 2 + 1 < Ls k} =>
      ∫ θ, wiredVillainDisorder (Ls k) β hβ ξ
          (⟨Ls k / 2, by have := k.2.2; omega⟩, ⟨Ls k / 2, by have := k.2.2; omega⟩) n
          ⟨k.2.1, k.2.2⟩ θ ∂villainLaw (Ls k) β hβ) atTop (𝓝 (D n))

end FroehlichSpencer.BKT

end
