/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.PlaneRotatorLimitWellDefined

/-! # The infinite-volume plane rotator two-point function -/

public section

namespace FroehlichSpencer.BKT

/-- The infinite-volume plane rotator two-point function `⟨cos (ξ (θ_j - θ_ℓ))⟩(β)`, `β ≥ 0`
(FS81 J p. 533; for `ξ = 1` it is `⟨S_j · S_ℓ⟩(β)`, (1.29)): the unique limit, as `Λ ↑ ℤ²`, of
the free-boundary finite-volume two-point functions (`existsUnique_tendsto_planeRotatorTwoPoint`). -/
@[expose] noncomputable def planeRotatorCorrelation (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ)
    (j ℓ : ℤ × ℤ) : ℝ :=
  Classical.choose (existsUnique_tendsto_planeRotatorTwoPoint β hβ ξ j ℓ).exists

end FroehlichSpencer.BKT

end
