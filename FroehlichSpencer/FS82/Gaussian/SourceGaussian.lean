/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Gaussian.SourceDualComplex
public import FroehlichSpencer.FS82.Gaussian.FiniteQuotientGaussian

/-!
# Source covariance and quotient Gaussian

This module instantiates the generic finite exact-complex Gaussian theory on
the star-transported source dual complex.

That complex retains its star-cell
orientations.

The lattice source operator `Π_{Λ*} δd` is not identified here;
the sign-twisted operator bridge belongs in `SourceOperatorBridge.lean` after
.
-/

public section

namespace FroehlichSpencer.FS82.Gaussian

open scoped InnerProductSpace


/-- Ambient covariance obtained by projecting onto co-closed fields and
applying the generic finite Hodge inverse. -/
@[expose] noncomputable def sourceDualAmbientCovariance {B : SourceBox} :=
  finiteComplexAmbientCovariance (sourceDualComplex B)


/-- Canonical quotient map from ambient edge fields. -/
@[expose] noncomputable def sourceDualQuotientMap {B : SourceBox} :=
  finiteComplexQuotientMap (sourceDualComplex B)


/-- The centered Gaussian on the gauge quotient induced by the source
covariance. -/
@[expose] noncomputable def sourceDualQuotientGaussian {B : SourceBox}
    (β : ℝ) (hβ : 0 ≤ β) :=
  finiteComplexQuotientGaussian (sourceDualComplex B) β hβ

theorem sourceDualQuotientGaussian_is_probability {B : SourceBox}
    {β : ℝ} (hβ : 0 ≤ β) :
    MeasureTheory.IsProbabilityMeasure (sourceDualQuotientGaussian (B := B) β hβ) :=
  finiteComplexQuotientGaussian_is_probability (sourceDualComplex B) hβ


theorem sourceDualAmbientCovariance_coClosed_apply {B : SourceBox}
    (μ : coClosed (sourceDualComplex B)) :
    sourceDualAmbientCovariance μ =
      (hodgeInverseOnCoClosed (sourceDualComplex B) μ :
        EuclideanSpace ℝ (SourceDualOneCells B)) :=
  finiteComplexAmbientCovariance_coClosed_apply (sourceDualComplex B) μ


/-- A co-closed test descends to a continuous linear functional on the gauge
quotient. -/
@[expose] noncomputable def sourceDualQuotientTestFunctional {B : SourceBox}
    (μ : coClosed (sourceDualComplex B)) :=
  finiteComplexQuotientTestFunctional (sourceDualComplex B) μ

theorem sourceDualQuotientTestFunctional_comp {B : SourceBox}
    (μ : coClosed (sourceDualComplex B)) :
    (sourceDualQuotientTestFunctional μ).comp (sourceDualQuotientMap (B := B)) =
      InnerProductSpace.toDualMap ℝ
        (EuclideanSpace ℝ (SourceDualOneCells B)) (μ : _) :=
  finiteComplexQuotientTestFunctional_comp (sourceDualComplex B) μ

theorem sourceDualQuotientGaussian_charFunDual {B : SourceBox} {β : ℝ}
    (hβ : 0 ≤ β) (μ : coClosed (sourceDualComplex B)) :
    MeasureTheory.charFun
      (MeasureTheory.Measure.map (sourceDualQuotientTestFunctional μ)
        (sourceDualQuotientGaussian (B := B) β hβ)) 1 =
      Complex.exp (-↑(inner ℝ (μ : EuclideanSpace ℝ (SourceDualOneCells B))
        ((β • sourceDualAmbientCovariance) μ) / 2)) :=
  finiteComplexQuotientGaussian_charFunDual (sourceDualComplex B) hβ μ

end FroehlichSpencer.FS82.Gaussian
end
