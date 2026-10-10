/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Surface.KuboQuantity

/-! # Kubo characterization of the diffusion coefficient -/

public section

open MeasureTheory Topology

namespace FroehlichSpencer

/-- A value `D` is the diffusion coefficient at an energy with positive IDS
derivative `r` when the Kubo expression tends to `r * D` as `ε ↓ 0`. -/
@[expose] def is_diffusion_coefficient (ν : ℕ) (hν : 0 < ν) (law : Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure law] (E r D : ℝ) : Prop :=
  0 < r ∧ 0 ≤ D ∧
    Filter.Tendsto
      (fun ε : {ε : ℝ // ε ≠ 0} => kuboQuantity ν hν law E ε)
      (Filter.comap Subtype.val (𝓝[>] (0 : ℝ)))
      (𝓝 (ENNReal.ofReal (r * D)))

end FroehlichSpencer

end
