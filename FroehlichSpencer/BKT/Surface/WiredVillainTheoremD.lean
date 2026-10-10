/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import FroehlichSpencer.BKT.Surface.WiredVillainDisorderLimit
import FroehlichSpencer.BKT.Provider.WiredVillainTheoremD

/-! # FS81 Theorem D for the Villain model in infinite volume, along wired boxes -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
FS81 Theorem D (J p. 534) for the Villain model in infinite volume, along the wired
boxes `Λ_L^zero` of the `villainLaw` centred at `0` (a boundary-condition variant: FS81's
thermodynamic limit is that of the free-boundary states (1.26)).

For each `ξ ∈ (0, 1)` there exists
some finite `β₀(ξ)` such that for `β > β₀(ξ)` a thermodynamic limit of the disorder expectations
exists, and every thermodynamic limit satisfies `⟨D^ξ_{0x}⟩(β) ≤ const (1 + |x|)^{-ξ²β''}` for some
positive `β'' = β''(ξ, β)`, where `x = (n, 0)` and `|x| = n`.
-/
theorem wiredVillain_disorderLimit_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      (∃ D : ℕ → ℝ, IsWiredVillainDisorderLimit β hβ ξ D) ∧
      ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, ∀ D : ℕ → ℝ, IsWiredVillainDisorderLimit β hβ ξ D →
        ∀ n : ℕ, D n ≤ A * (1 + (n : ℝ)) ^ (-(ξ ^ 2 * β'')) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.wiredVillain_disorderLimit_upper_bound
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
