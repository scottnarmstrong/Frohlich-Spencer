/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.Finsupp.Basic
public import FroehlichSpencer.BKT.Surface.PeriodicHardCorePartition

/-! # The field second moment of the hard-core sine-Gordon state on a periodic square -/

open MeasureTheory
open Fin.CommRing

@[expose] public section

namespace FroehlichSpencer.BKT

/-- FS81 (1.16) on a periodic box (J p. 531): the second moment
`⟨φ(g)²⟩ = Z⁻¹ ∫ φ(g)² ∏_{x ∈ Λ} (1 + z cos φ(x)) dμ_{β,Ω}(φ)`, `φ(g) = ∑_x g(x) φ(x)`, of the
hard-core sine-Gordon state with charges in `Λ ⊂ ℤ²` and the Gaussian field on `Ω = Λ_L^per`
(`periodicHardCorePartition`), for a finitely supported real test function `g` on `ℤ²`. The
state is a signed measure when `z > 1`; the value is the normalized integral. -/
noncomputable def periodicHardCoreSecondMoment (β : ℝ) (hβ : 0 < β) (z : ℝ)
    (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (L : ℕ) (hL : 1 < L) : ℝ :=
  haveI : NeZero L := ⟨by omega⟩
  (∫ φ : Fin L × Fin L → ℝ, (g.sum fun x a => a * φ ((x.1 : Fin L), (x.2 : Fin L))) ^ 2 *
      ∏ x ∈ Λ, (1 + z * Real.cos (φ ((x.1 : Fin L), (x.2 : Fin L))))
    ∂gffLaw (squarePeriodic L) (squarePeriodic_connected L hL) β⁻¹ (inv_pos.mpr hβ) 0) /
    periodicHardCorePartition β hβ z Λ L hL

end FroehlichSpencer.BKT

end
