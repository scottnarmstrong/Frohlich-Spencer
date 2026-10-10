/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.HardCoreSecondMoment

/-! # Characterization of the free-boundary hard-core field second moment -/

open Filter Topology

public section

namespace FroehlichSpencer.BKT

/-- `hardCoreSecondMoment β hβ z hz Λ g hgΛ hg` is the limit, and the only limit, of the
hard-core sine-Gordon second moments on the periodic squares `Λ_{2n+2}^per`. -/
theorem hardCoreSecondMoment_spec (β : ℝ) (hβ : 0 < β) (z : ℝ) (hz : 0 ≤ z)
    (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
    (hg : (g.sum fun _ a => a) = 0) (m : ℝ) :
    Tendsto (fun n : ℕ =>
      periodicHardCoreSecondMoment β hβ z Λ g (2 * n + 2) (Nat.one_lt_succ_succ (2 * n)))
      atTop (𝓝 m) ↔
      m = hardCoreSecondMoment β hβ z hz Λ g hgΛ hg := by
  have h := existsUnique_tendsto_periodicHardCoreSecondMoment β hβ z hz Λ g hgΛ hg
  have hspec := Classical.choose_spec h.exists
  constructor
  · intro hm
    exact h.unique hm hspec
  · rintro rfl
    exact hspec

end FroehlichSpencer.BKT

end
