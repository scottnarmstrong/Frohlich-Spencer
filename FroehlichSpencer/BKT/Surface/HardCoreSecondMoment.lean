/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.HardCoreSecondMomentWellDefined

/-! # The field second moment of the free-boundary hard-core sine-Gordon state -/

public section

namespace FroehlichSpencer.BKT

/-- The field second moment `⟨φ(g)²⟩_Λ(β, z)` of the hard-core Coulomb gas in the finite region
`Λ ⊂ ℤ²` with free boundary conditions, in the sine-Gordon representation (FS81 (1.16), (5.1),
(5.2), J pp. 531, 563–564), for `β > 0`, `z ≥ 0` and a neutral test function `g` supported in
`Λ`: the unique limit of the periodic-box second moments, `dμ_β = lim dμ_{β,Ω}`
(`existsUnique_tendsto_periodicHardCoreSecondMoment`). -/
@[expose] noncomputable def hardCoreSecondMoment (β : ℝ) (hβ : 0 < β) (z : ℝ) (hz : 0 ≤ z)
    (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
    (hg : (g.sum fun _ a => a) = 0) : ℝ :=
  Classical.choose
    (existsUnique_tendsto_periodicHardCoreSecondMoment β hβ z hz Λ g hgΛ hg).exists

end FroehlichSpencer.BKT

end
