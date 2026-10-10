/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Topology.Instances.Real.Lemmas
public import FroehlichSpencer.BKT.Surface.PlaneRotatorLaw
import FroehlichSpencer.BKT.Provider.PlaneRotatorLimitWellDefined

/-! # The free thermodynamic limit of the plane rotator two-point function -/

open MeasureTheory Filter Topology

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
for `β ≥ 0`, every integer harmonic `ξ` and sites `j, ℓ ∈ ℤ²`, the
finite-volume two-point functions `⟨cos (ξ (θ_j - θ_ℓ))⟩_Λ(β)` of the free-boundary states (1.26)
converge as `Λ ↑ ℤ²` through the finite regions containing `j` and `ℓ`, to a unique limit
(FS81 J p. 533: "The thermodynamic limit, `⟨-⟩(β)`, of the states `{⟨·⟩_Λ(β)}` is known to
exist, a consequence of correlation inequalities [11]"; J p. 535: independent of `{Λ}`).
-/
theorem existsUnique_tendsto_planeRotatorTwoPoint (β : ℝ) (hβ : 0 ≤ β) (ξ : ℤ)
    (j ℓ : ℤ × ℤ) :
    ∃! c : ℝ, Tendsto (fun Λ : {Λ : Finset (ℤ × ℤ) // j ∈ Λ ∧ ℓ ∈ Λ} =>
      ∫ θ : Λ.1 → ℝ, Real.cos ((ξ : ℝ) * (θ ⟨j, Λ.2.1⟩ - θ ⟨ℓ, Λ.2.2⟩))
        ∂planeRotatorLaw β Λ.1) atTop (𝓝 c) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.existsUnique_tendsto_planeRotatorTwoPoint β hβ ξ j ℓ
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
