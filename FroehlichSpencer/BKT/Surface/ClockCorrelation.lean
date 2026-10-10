/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ClockLimitWellDefined

/-! # The infinite-volume `ℤ_n` clock two-point function -/

public section

namespace FroehlichSpencer.BKT

/-- The infinite-volume `ℤ_n` clock two-point function `⟨cos (ξ (θ_j - θ_ℓ))⟩^{(n)}(β)`, `n ≥ 1`,
`β ≥ 0` (FS81 J p. 585): the unique limit, as `Λ ↑ ℤ²`, of the free-boundary finite-volume clock
two-point functions (`existsUnique_tendsto_clockTwoPoint`). -/
@[expose] noncomputable def clockCorrelation (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ)
    (j ℓ : ℤ × ℤ) : ℝ :=
  Classical.choose (existsUnique_tendsto_clockTwoPoint n hn β hβ ξ j ℓ).exists

end FroehlichSpencer.BKT

end
