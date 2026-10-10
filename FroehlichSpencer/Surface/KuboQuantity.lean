/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import FroehlichSpencer.Surface.ConfigurationMeasure
public import FroehlichSpencer.Surface.GreenFunction
public import FroehlichSpencer.Surface.LatticeLength

/-! # The nonnegative Kubo expression -/

public section

open MeasureTheory

namespace FroehlichSpencer

/-- The nonnegative extended-real expression on the right side of (1.15), at
a nonzero imaginary part. `ENNReal` integration and summation retain divergence
as `⊤`. -/
@[expose] noncomputable def kuboQuantity (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure law] (E : ℝ) (ε : {ε : ℝ // ε ≠ 0}) : ENNReal :=
  ENNReal.ofReal (2 * ε.1 ^ 2 / (Real.pi * (ν : ℝ))) *
    ∑' x : Site ν,
      ENNReal.ofReal ((latticeLength ν x) ^ 2) *
        ∫⁻ v : Configuration ν,
          ENNReal.ofReal
            (‖greenFunction ν hν ((E : ℂ) + (ε.1 : ℂ) * Complex.I)
              (by simpa using ε.2) v 0 x‖ ^ 2)
          ∂configurationMeasure ν law

end FroehlichSpencer

end
