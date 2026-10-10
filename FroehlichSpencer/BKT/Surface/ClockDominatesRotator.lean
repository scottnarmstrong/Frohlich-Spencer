/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ClockCorrelation
public import FroehlichSpencer.BKT.Surface.PlaneRotatorCorrelation
import FroehlichSpencer.BKT.Provider.ClockDominatesRotator

/-! # FS81 Theorem 7.1 (1): the `ℤ_n` clock correlations dominate the plane rotator -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
FS81 Theorem 7.1 (1) (J p. 585).

For all `ξ = 1, …, n - 1`,
`⟨e^{iξ(θ_0 - θ_x)}⟩^{(n)}(β) ≥ ⟨e^{iξ(θ_0 - θ_x)}⟩(β)`: the infinite-volume `ℤ_n` clock two-point
function dominates the plane-rotator one at the same `β`.

Both are the free thermodynamic limits of
the real cosine correlations `⟨cos (ξ (θ_0 - θ_x))⟩` (equal to the exponential ones by the
`θ ↦ -θ` symmetry, (1.29)).
-/
theorem planeRotatorCorrelation_le_clockCorrelation (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β)
    (ξ : ℤ) (hξ₁ : 1 ≤ ξ) (hξ₂ : ξ ≤ (n : ℤ) - 1) (x : ℤ × ℤ) :
    planeRotatorCorrelation β hβ ξ 0 x ≤ clockCorrelation n hn β hβ ξ 0 x :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.planeRotatorCorrelation_le_clockCorrelation n hn β hβ ξ hξ₁ hξ₂ x
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
