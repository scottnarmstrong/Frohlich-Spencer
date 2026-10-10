/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.DualComplexD
public import FroehlichSpencer.FS82.Gaussian.FiniteQuotientGaussian

/-!
# Quotient Gaussian on the degree `d - 2` dual forms

For every `d ≥ 3`, the finite exact-one complex from `DualComplexD` has its
co-closed Gaussian quotient on dual `(d - 2)`-forms.  The characteristic
formula is inherited from the generic finite-complex quotient construction.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open MeasureTheory
open ProbabilityTheory
open scoped InnerProductSpace

variable {d : ℕ} (hd : 3 ≤ d) (B : Box d)

/-- The co-closed degree-`d - 2` dual forms in the grounded box complex. -/
noncomputable abbrev DualDCoClosed := coClosed (dualDExactOneComplex hd B)

/-- The quotient of degree-`d - 2` dual forms by exact forms. -/
noncomputable abbrev DualDQuotient := FiniteGaugeQuotient (dualDExactOneComplex hd B)

/-- The source Gaussian on the quotient of dual `(d - 2)`-forms. -/
noncomputable def dualDQuotientGaussian (β : ℝ) (hβ : 0 ≤ β) :
    Measure (DualDQuotient hd B) :=
  finiteComplexQuotientGaussian (dualDExactOneComplex hd B) β hβ


/-- The canonical quotient test associated with a co-closed dual form. -/
noncomputable def dualDQuotientTest (μ : DualDCoClosed hd B) :
    StrongDual ℝ (DualDQuotient hd B) :=
  finiteComplexQuotientTestFunctional (dualDExactOneComplex hd B) μ

/-- The quotient Gaussian characteristic function on every co-closed test.
The covariance is the inverse of `d₁† d₁` on the co-closed subspace. -/
theorem dualDQuotientGaussian_characteristic {β : ℝ} (hβ : 0 ≤ β)
    (μ : DualDCoClosed hd B) :
    charFun (Measure.map (dualDQuotientTest hd B μ)
      (dualDQuotientGaussian hd B β hβ)) 1 =
      Complex.exp (-↑(inner ℝ (μ : EuclideanSpace ℝ (DualDForm B (d - 2)))
        ((β • finiteComplexAmbientCovariance (dualDExactOneComplex hd B)) μ) / 2)) := by
  exact finiteComplexQuotientGaussian_charFunDual
    (dualDExactOneComplex hd B) hβ μ

/-- On the co-closed subspace, the ambient covariance is exactly the Hodge
inverse, so the characteristic exponent has the usual quotient form. -/
theorem dualDQuotientGaussian_characteristic_hodge {β : ℝ} (hβ : 0 ≤ β)
    (μ : DualDCoClosed hd B) :
    charFun (Measure.map (dualDQuotientTest hd B μ)
      (dualDQuotientGaussian hd B β hβ)) 1 =
      Complex.exp (-↑(β * quotientCovarianceQuadratic
        (dualDExactOneComplex hd B) μ / 2)) := by
  rw [dualDQuotientGaussian_characteristic hd B hβ μ]
  congr 1
  simp only [LinearMap.smul_apply]
  rw [finiteComplexAmbientCovariance_coClosed_apply]
  rw [quotientCovarianceQuadratic]
  rw [real_inner_smul_right]

/-- The source-frequency characteristic, with the frequency scaled by `2π`. -/
theorem dualDQuotientGaussian_characteristic_twoPi {β : ℝ} (hβ : 0 ≤ β)
    (μ : DualDCoClosed hd B) :
    charFun (Measure.map (dualDQuotientTest hd B ((2 * Real.pi) • μ))
      (dualDQuotientGaussian hd B β hβ)) 1 =
      Complex.exp (-((β * (2 * Real.pi) ^ 2 * quotientCovarianceQuadratic
        (dualDExactOneComplex hd B) μ / 2 : ℝ) : ℂ)) := by
  rw [dualDQuotientGaussian_characteristic_hodge hd B hβ ((2 * Real.pi) • μ)]
  apply congrArg Complex.exp
  apply congrArg Neg.neg
  apply congrArg (fun x : ℝ => (x : ℂ))
  have hV : hodgeInverseOnCoClosed (dualDExactOneComplex hd B)
      ((2 * Real.pi) • μ) = (2 * Real.pi) •
        hodgeInverseOnCoClosed (dualDExactOneComplex hd B) μ := by
    exact map_smul _ _ _
  simp only [quotientCovarianceQuadratic, Submodule.coe_smul]
  rw [hV]
  simp only [Submodule.coe_smul]
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- The all-dimensional source phase attached to a co-closed current and a
co-closed path test. -/
noncomputable def dualDPathPhase {β : ℝ} (hβ : 0 ≤ β)
    (ρ τ : DualDCoClosed hd B) : ℂ :=
  charFun (Measure.map (dualDQuotientTest hd B ((2 * Real.pi) • ρ))
    (dualDQuotientGaussian hd B β hβ)) 1 *
    Complex.exp (Complex.I * (2 * Real.pi : ℂ) *
      ((inner ℝ (ρ : EuclideanSpace ℝ (DualDForm B (d - 2)))
        (τ : EuclideanSpace ℝ (DualDForm B (d - 2))) : ℝ) : ℂ))

/-- The source phase is the quotient Gaussian characteristic times its
Fourier tilt. -/
theorem dualDPathPhase_eq {β : ℝ} (hβ : 0 ≤ β)
    (ρ τ : DualDCoClosed hd B) :
    dualDPathPhase hd B hβ ρ τ =
      Complex.exp (-((β * (2 * Real.pi) ^ 2 * quotientCovarianceQuadratic
        (dualDExactOneComplex hd B) ρ / 2 : ℝ) : ℂ)) *
      Complex.exp (Complex.I * (2 * Real.pi : ℂ) *
        ((inner ℝ (ρ : EuclideanSpace ℝ (DualDForm B (d - 2)))
          (τ : EuclideanSpace ℝ (DualDForm B (d - 2))) : ℝ) : ℂ)) := by
  rw [dualDPathPhase, dualDQuotientGaussian_characteristic_twoPi hd B hβ ρ]

end FroehlichSpencer.FS82.XY

end
