/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Partition function for the finite-volume field

The definition records the normalizing integral in KP (1.3), p. 2. Integrability and strict positivity on connected graphs give the associated probability measure.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

open MeasureTheory Multigraph

variable {V : Type u} {E : Type v}

/-- The KP partition-function integral associated to the rooted density
(1.3), p. 2. -/
noncomputable def gffPartitionFunction (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (β : ℝ) (root : V) : ℝ :=
  ∫ φ, gffDensity G β root φ ∂(volume : Measure (V → ℝ))

/-- The partition function is the integral of the candidate KP density. -/
theorem gffPartitionFunction_eq_integral (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (β : ℝ) (root : V) :
    gffPartitionFunction G β root =
      ∫ φ, gffDensity G β root φ ∂(volume : Measure (V → ℝ)) := rfl

end FroehlichSpencer.BKT
