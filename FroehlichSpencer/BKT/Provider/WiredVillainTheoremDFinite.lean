/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.WiredVillainDisorder
public import FroehlichSpencer.BKT.Surface.WiredVillainDisorder
public import FroehlichSpencer.BKT.Surface.VillainLaw
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.wiredVillain_disorder_upper_bound`

From the internal `villainDisorder_bound` through `Bridge.WiredVillainDisorder.wired_bound`, with
`β'' = c η² β / ξ²`, `η = min(ξ, 1 − ξ)`, and the constant `2`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.VillainDisorder
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap dipoleGap_pos)
open FroehlichSpencer.BKT.Bridge.WiredVillainDisorder


theorem wiredVillain_disorder_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, ∀ (L : ℕ) (o : Fin L × Fin L) (n : ℕ)
        (hfit : o.1.val + n < L ∧ o.2.val + 1 < L),
        ∫ θ, wiredVillainDisorder L β hβ ξ o n hfit θ ∂villainLaw L β hβ ≤
          A * (1 + (n : ℝ)) ^ (-(ξ ^ 2 * β'')) := by
  obtain ⟨c, hc, h⟩ := wired_bound
  intro ξ hξ0 hξ1
  obtain ⟨β₀, -, hD⟩ := h ξ hξ0 hξ1
  refine ⟨β₀, fun β hβ hββ₀ => ⟨c * dipoleGap ξ ^ 2 * β / ξ ^ 2, ?_, 2, fun L o n hfit => ?_⟩⟩
  · have := dipoleGap_pos hξ0 hξ1
    positivity
  · rw [exponent_eq hξ0, add_comm (1 : ℝ)]
    exact (hD β hβ hββ₀ L o n hfit).2

end FroehlichSpencer.BKT.Provider

end
