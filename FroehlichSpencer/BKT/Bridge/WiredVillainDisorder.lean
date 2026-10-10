/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.WiredVillainDisorder
public import FroehlichSpencer.BKT.Surface.VillainWellDefined
public import FroehlichSpencer.BKT.VillainDisorder.TheoremD
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
The string of `n = 0` bonds has `D = 1` under the KP
law (`integral_wiredVillainDisorder_zero`, from the KP gate
`isProbabilityMeasure_villainLaw`).

So the internal `villainDisorder_bound` gives
`0 ≤ ⟨D⟩ ≤ 2 (n + 1)^{-c η² β}` on every wired box for all `n` (`wired_bound`,
`η = min(ξ, 1 − ξ)`); `exponent_eq` rewrites the exponent as `ξ² β''` with `β'' = c η² β / ξ²`.

The
two wired roots are proved in `BKT/Provider/`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.WiredVillainDisorder

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.VillainDisorder
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap dipoleGap_pos)

theorem wiredVillainDisorder_eq {L : ℕ} (β : ℝ) (hβ : 0 < β) (ξ : ℝ) (o : Fin L × Fin L) (n : ℕ)
    (hfit : o.1.val + n < L ∧ o.2.val + 1 < L) :
    wiredVillainDisorder L β hβ ξ o n hfit = villainDisorderInternal β ξ o n hfit := rfl

theorem integral_wiredVillainDisorder_zero (L : ℕ) (β ξ : ℝ) (hβ : 0 < β) (o : Fin L × Fin L)
    (hfit : o.1.val + 0 < L ∧ o.2.val + 1 < L) :
    ∫ θ, wiredVillainDisorder L β hβ ξ o 0 hfit θ ∂villainLaw L β hβ = 1 := by
  have := isProbabilityMeasure_villainLaw L β hβ
  simp [wiredVillainDisorder]

/-- The bound on every wired box, for all `n` (with `n = 0` included). -/
theorem wired_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ (β : ℝ) (hβ : 0 < β), β₀ < β → ∀ (L : ℕ) (o : Fin L × Fin L) (n : ℕ)
        (hfit : o.1.val + n < L ∧ o.2.val + 1 < L),
        0 ≤ ∫ θ, wiredVillainDisorder L β hβ ξ o n hfit θ ∂villainLaw L β hβ ∧
          ∫ θ, wiredVillainDisorder L β hβ ξ o n hfit θ ∂villainLaw L β hβ ≤
            2 * ((n : ℝ) + 1) ^ (-(c * dipoleGap ξ ^ 2 * β)) := by
  obtain ⟨c, hc, h⟩ := villainDisorder_bound
  refine ⟨c, hc, fun ξ hξ0 hξ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hD⟩ := h (dipoleGap ξ) (dipoleGap_pos hξ0 hξ1)
  refine ⟨β₀, hβ₀, fun β hβ hββ₀ L o n hfit => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [integral_wiredVillainDisorder_zero]
    simp
  · exact hD L β hβ hββ₀ ξ hξ0 hξ1 le_rfl o n hfit hn

theorem exponent_eq {c ξ β : ℝ} (hξ : 0 < ξ) :
    ξ ^ 2 * (c * dipoleGap ξ ^ 2 * β / ξ ^ 2) = c * dipoleGap ξ ^ 2 * β := by
  field_simp

end FroehlichSpencer.BKT.Bridge.WiredVillainDisorder

end
