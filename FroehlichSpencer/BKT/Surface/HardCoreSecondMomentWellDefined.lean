/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import FroehlichSpencer.BKT.Surface.PeriodicHardCoreSecondMoment
import FroehlichSpencer.BKT.Provider.HardCoreSecondMomentWellDefined

/-! # The free-boundary limit of the hard-core sine-Gordon field second moment -/

open Filter Topology

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
FS81 `dμ_β = lim dμ_{β,Ω}` as `Ω ↑ ℤ²` through periodic boxes (J p. 531, after
(1.14)).

For `β > 0`, `z ≥ 0`, a finite region `Λ ⊂ ℤ²` and a finitely supported real `g` with
`supp g ⊆ Λ` and `∑_x g(x) = 0`, the hard-core sine-Gordon second moments `⟨φ(g)²⟩` with charges
in `Λ` on the periodic squares `Λ_{2n+2}^per` converge as `n → ∞`, to a unique limit.
-/
theorem existsUnique_tendsto_periodicHardCoreSecondMoment (β : ℝ) (hβ : 0 < β) (z : ℝ)
    (hz : 0 ≤ z) (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
    (hg : (g.sum fun _ a => a) = 0) :
    ∃! m : ℝ, Tendsto (fun n : ℕ =>
      periodicHardCoreSecondMoment β hβ z Λ g (2 * n + 2) (Nat.one_lt_succ_succ (2 * n)))
      atTop (𝓝 m) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.existsUnique_tendsto_periodicHardCoreSecondMoment β hβ z hz Λ g hgΛ hg
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
