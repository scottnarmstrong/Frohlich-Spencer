/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import FroehlichSpencer.BKT.Surface.SOSDirichletLaw
import FroehlichSpencer.BKT.Provider.SOSRoughening

/-! # The roughening transition of the solid-on-solid model -/

open MeasureTheory

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
the roughening transition of the two-dimensional solid-on-solid model (FS81 §7.2,
Remark 2, J p. 590: "It follows from a standard low-temperature (Peierls contour) expansion that
⟨[φ(0)-φ(x)]²⟩_A^0(β) is bounded uniformly in A and in x∈A, provided β is large.

This and (7.18)
establish the existence of a roughening transition, as β is varied."), in boxes with Dirichlet
boundary conditions.

There are `0 < β₀ < β₁` such that for `0 < β ≤ β₀` (high temperature) the
height fluctuations `⟨[φ(u) - φ(v)]²⟩` are unbounded over boxes and sites (the surface is rough),
and for `β ≥ β₁` (low temperature) they are bounded uniformly in `β`, in the box and in the sites
(the surface is smooth).
-/
theorem sos_roughening_transition :
    ∃ β₀ β₁ : ℝ, 0 < β₀ ∧ β₀ < β₁ ∧
      (∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ → ∀ K : ℝ, ∃ (L : ℕ) (u v : Fin L × Fin L),
        ENNReal.ofReal K < ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ) ∧
      ∃ C : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₁ ≤ β → ∀ (L : ℕ) (u v : Fin L × Fin L),
        ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ ≤ ENNReal.ofReal C :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.sos_roughening_transition
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
