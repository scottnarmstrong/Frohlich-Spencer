/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ClockCorrelation

/-! # Characterization of the infinite-volume clock two-point function -/

open MeasureTheory Filter Topology

public section

namespace FroehlichSpencer.BKT

/-- `clockCorrelation n hn β hβ ξ j ℓ` is the limit, and the only limit, of the free-boundary
finite-volume clock two-point functions `⟨cos (ξ (θ_j - θ_ℓ))⟩_Λ^{(n)}(β)` as `Λ ↑ ℤ²`. -/
theorem clockCorrelation_spec (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ) (j ℓ : ℤ × ℤ)
    (c : ℝ) :
    Tendsto (fun Λ : {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ} =>
      ∫ θ : Λ.1 → ℝ, Real.cos ((ξ : ℝ) * (θ ⟨j, Λ.2.1⟩ - θ ⟨ℓ, Λ.2.2⟩))
        ∂clockLaw n hn β Λ.1) atTop (𝓝 c) ↔
      c = clockCorrelation n hn β hβ ξ j ℓ := by
  have h := existsUnique_tendsto_clockTwoPoint n hn β hβ ξ j ℓ
  have hspec := Classical.choose_spec h.exists
  constructor
  · intro hc
    exact h.unique hc hspec
  · rintro rfl
    exact hspec

end FroehlichSpencer.BKT

end
