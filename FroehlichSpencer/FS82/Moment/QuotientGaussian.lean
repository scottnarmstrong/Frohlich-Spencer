/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Moment.SourceCoercivity
public import FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section

set_option linter.style.haveILetI false

open MeasureTheory

namespace FroehlichSpencer.FS82.Moment.QuotientGaussian

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor

variable {B : Box 4}


/-- The scalar Gaussian character of a physical source current. -/
noncomputable def sourcePhysicalGaussianCharacter (β : ℝ)
    (j : IntegerCurrent B) (hdiv : currentDivergence j = 0) : ℝ :=
  Real.exp (-(β / 2) *
    Gaussian.quotientCovarianceQuadratic
      (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero)
      (SourceCoercivity.sourcePhysicalCurrentCoClosed Cubical.originZero j hdiv))


end FroehlichSpencer.FS82.Moment.QuotientGaussian

end
