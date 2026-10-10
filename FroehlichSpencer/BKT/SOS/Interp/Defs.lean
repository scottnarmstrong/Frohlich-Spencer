/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselInterp.Defs

/-!
# The Appendix C interpolation of `e^{-β|n|}` (FS81, J p.599)

For the solid-on-solid model FS81 §7.2 needs an analytic interpolation `I_β(φ)` of the edge
weights `e^{-β|n|}`, `n ∈ ℤ`. Appendix C defines it explicitly:

`L_β(φ) = exp[-β^{2/3}(1 + β^{2/3}φ²)^{1/2}]`,
`E_β(φ) = exp[-Σ_n (β|n| - β^{2/3}(1 + β^{2/3}n²)^{1/2}) sin²((φ-n)π)/((φ-n)²π²)]`,
`I_β = L_β E_β` (C.1).

This file contains the literal definitions, with the principal square root. The kernel
`sin²(πz)/(π²z²)` is the one of Appendix B (`BesselInterp.sincSq`). Properties are proved in the
sibling modules.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Interp

open Complex

/-- FS81 (C.1): `L_β(φ) = exp[-β^{2/3}(1 + β^{2/3}φ²)^{1/2}]`. -/
def sosDebye (β : ℝ) (φ : ℂ) : ℂ :=
  Complex.exp (-((β ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
    (1 + ((β ^ (2 / 3 : ℝ) : ℝ) : ℂ) * φ ^ 2) ^ (1 / 2 : ℂ))

/-- The coefficients `β|n| - β^{2/3}(1 + β^{2/3}n²)^{1/2}` of (C.1). -/
def sosDefect (β : ℝ) (n : ℤ) : ℝ :=
  β * |(n : ℝ)| - β ^ (2 / 3 : ℝ) * Real.sqrt (1 + β ^ (2 / 3 : ℝ) * (n : ℝ) ^ 2)

/-- The exponent of `E_β` in (C.1): `Σ_n (β|n| - β^{2/3}(1+β^{2/3}n²)^{1/2}) K(φ - n)`. -/
def sosSeries (β : ℝ) (φ : ℂ) : ℂ :=
  ∑' n : ℤ, (sosDefect β n : ℂ) * Rotator.BesselInterp.sincSq (φ - n)

/-- FS81 (C.1): `E_β(φ) = exp[-Σ_n (β|n| - β^{2/3}(1+β^{2/3}n²)^{1/2}) sin²((φ-n)π)/((φ-n)²π²)]`. -/
def sosFactor (β : ℝ) (φ : ℂ) : ℂ := Complex.exp (-sosSeries β φ)

/-- FS81 Appendix C: the interpolation `I_β = L_β E_β` of `e^{-β|n|}`. -/
def sosInterp (β : ℝ) (φ : ℂ) : ℂ := sosDebye β φ * sosFactor β φ

end FroehlichSpencer.BKT.SOS.Interp
