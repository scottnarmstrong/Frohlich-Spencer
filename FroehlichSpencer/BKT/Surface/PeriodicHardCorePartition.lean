/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FroehlichSpencer.BKT.Surface.GFFLaw
public import FroehlichSpencer.BKT.Surface.SquarePeriodicConnected

/-! # The hard-core sine-Gordon partition function on a periodic square -/

open MeasureTheory
open Fin.CommRing

@[expose] public section

namespace FroehlichSpencer.BKT

/--
FS81 (1.15)–(1.16) and (5.1) on a periodic box (J pp. 531, 563): the partition function
`Z = ∫ ∏_{x ∈ Λ} (1 + z cos φ(x)) dμ_{β,Ω}(φ)` of the hard-core gas with charges in the finite
region `Λ ⊂ ℤ²`, in the sine-Gordon representation, where `Ω = Λ_L^per` (`L > 1`) carries the
Gaussian field `μ_{β,Ω}` with covariance `β (-Δ_Ω)⁻¹`: the `gffLaw` at KP inverse
temperature `β⁻¹`, normalized to `[-π, π)` at the vertex `0`.

A site `x ∈ Λ` is placed at
`(x₁ mod L, x₂ mod L)`.
-/
noncomputable def periodicHardCorePartition (β : ℝ) (hβ : 0 < β) (z : ℝ) (Λ : Finset (ℤ × ℤ))
    (L : ℕ) (hL : 1 < L) : ℝ :=
  haveI : NeZero L := ⟨by omega⟩
  ∫ φ : Fin L × Fin L → ℝ, ∏ x ∈ Λ, (1 + z * Real.cos (φ ((x.1 : Fin L), (x.2 : Fin L))))
    ∂gffLaw (squarePeriodic L) (squarePeriodic_connected L hL) β⁻¹ (inv_pos.mpr hβ) 0

end FroehlichSpencer.BKT

end
