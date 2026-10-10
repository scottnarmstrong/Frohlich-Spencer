/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FroehlichSpencer.BKT.Surface.VillainLaw
public import FroehlichSpencer.BKT.Surface.WiredVillainDisorder
import FroehlichSpencer.BKT.Provider.WiredVillainTheoremDFinite

/-! # FS81 Theorem D for the Villain model on the wired boxes, uniformly in the box -/

open MeasureTheory

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
FS81 Theorem D (J p. 534) for the Villain model on the wired boxes `Λ_L^zero` of
the `villainLaw` (a boundary-condition variant: FS81's states (1.26) are free-boundary).

For
each `ξ ∈ (0, 1)` there exists some finite `β₀(ξ)` such that for `β > β₀(ξ)`,
`⟨D^ξ_{0x}⟩(β) ≤ const (1 + |x|)^{-ξ²β''}` for some positive `β'' = β''(ξ, β)`, where
`x = (n, 0)`, `|x| = n`, and the constant does not depend on the box, the position of the string or
`n`.
-/
theorem wiredVillain_disorder_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, ∀ (L : ℕ) (o : Fin L × Fin L) (n : ℕ)
        (hfit : o.1.val + n < L ∧ o.2.val + 1 < L),
        ∫ θ, wiredVillainDisorder L β hβ ξ o n hfit θ ∂villainLaw L β hβ ≤
          A * (1 + (n : ℝ)) ^ (-(ξ ^ 2 * β'')) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.wiredVillain_disorder_upper_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
