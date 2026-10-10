/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Appendix B interpolation of the plane-rotator Bessel weights

FS81 (J p.576 and Appendix B, J pp.597–599) replaces the plane-rotator dual edge weight
`I_β(n) = (2π)⁻¹ ∫₀^{2π} e^{β cos θ} e^{inθ} dθ` (the `n`th modified Bessel function at `β`, with the
order as the argument) by a function of a complex order `φ`. The construction is explicit:
`I_β(φ) = L_β(φ) E_β(φ)`, where `L_β` is the uniform (Debye) leading term

`L_β(φ) = (2π)^{-1/2} [β(1+φ²/β²)^{1/2}]^{-1/2} exp[-φ sinh⁻¹(φ/β) + β(1+φ²/β²)^{1/2}]`

and `E_β(φ) = exp Σₙ (ln I_β(n) − ln L_β(n)) sin²((φ−n)π)/((φ−n)²π²)` (B.14). This file contains the
literal definitions, with principal branches. Their properties are proved in the sibling modules.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.BesselInterp

open Complex
open scoped Real

/-- FS81 (B.1) and property (a), J pp.576, 597: the Fourier coefficient
`I_β(n) = (2π)⁻¹ ∫₀^{2π} e^{β cos θ} e^{inθ} dθ`. -/
def besselCoeff (β : ℝ) (n : ℤ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, Complex.exp (β * Real.cos θ) * Complex.exp (n * θ * I)

/-- The real form `(2π)⁻¹ ∫₀^{2π} e^{β cos θ} cos (nθ) dθ` of `besselCoeff`. -/
def besselCoeffRe (β : ℝ) (n : ℤ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, Real.exp (β * Real.cos θ) * Real.cos (n * θ)

/-- The principal complex inverse hyperbolic sine `sinh⁻¹ w = log (w + (1 + w²)^{1/2})`. -/
def carsinh (w : ℂ) : ℂ := Complex.log (w + (1 + w ^ 2) ^ (1 / 2 : ℂ))

/-- FS81 J p.599: `L_β(φ) = (2π)^{-1/2} [β(1+φ²/β²)^{1/2}]^{-1/2}
exp[-φ sinh⁻¹(φ/β) + β(1+φ²/β²)^{1/2}]`, with principal branches. -/
def debye (β : ℝ) (φ : ℂ) : ℂ :=
  ((Real.sqrt (2 * π))⁻¹ : ℂ) * ((β : ℂ) * (1 + φ ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ)) ^ (-(1 / 2) : ℂ) *
    Complex.exp (-φ * carsinh (φ / β) + β * (1 + φ ^ 2 / (β : ℂ) ^ 2) ^ (1 / 2 : ℂ))

/-- The real form of `L_β` on the real axis. -/
def debyeRe (β x : ℝ) : ℝ :=
  (Real.sqrt (2 * π))⁻¹ * (β * Real.sqrt (1 + x ^ 2 / β ^ 2)) ^ (-(1 / 2) : ℝ) *
    Real.exp (-x * Real.arsinh (x / β) + β * Real.sqrt (1 + x ^ 2 / β ^ 2))

/-- The kernel `sin²(πz)/(π²z²)` of (B.14), with its removable value `1` at `z = 0`. -/
def sincSq (z : ℂ) : ℂ :=
  if z = 0 then 1 else Complex.sin (π * z) ^ 2 / ((π : ℂ) ^ 2 * z ^ 2)

/-- The coefficients `ln I_β(n) − ln L_β(n)` of (B.14). -/
def logDefect (β : ℝ) (n : ℤ) : ℝ :=
  Real.log (besselCoeffRe β n) - Real.log (debyeRe β n)

/-- The exponent of (B.14): `Σₙ (ln I_β(n) − ln L_β(n)) sin²((φ−n)π)/((φ−n)²π²)`. -/
def defectSeries (β : ℝ) (φ : ℂ) : ℂ :=
  ∑' n : ℤ, (logDefect β n : ℂ) * sincSq (φ - n)

/-- FS81 (B.14): `E_β(φ) = exp Σₙ (ln I_β(n) − ln L_β(n)) sin²((φ−n)π)/((φ−n)²π²)`. -/
def defectFactor (β : ℝ) (φ : ℂ) : ℂ := Complex.exp (defectSeries β φ)

/-- FS81 Appendix B, J p.599: the interpolation `I_β(φ) = L_β(φ) E_β(φ)` of the Bessel weights
in the order variable `φ`. -/
def besselInterp (β : ℝ) (φ : ℂ) : ℂ := debye β φ * defectFactor β φ

end FroehlichSpencer.BKT.Rotator.BesselInterp
