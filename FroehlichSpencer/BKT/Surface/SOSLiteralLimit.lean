/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import FroehlichSpencer.BKT.Surface.SOSLiteralDiffLaw

/-! # Limit points of FS81's solid-on-solid states as `Ω ↗ ℤ²` -/

open MeasureTheory Filter Topology

@[expose] public section

namespace FroehlichSpencer.BKT

/-- `ν` is a vague limit point, as `Ω ↗ ℤ²`, of FS81's states (7.16) read through the height
differences `φ(z) - φ(w)`, `z ∈ A` (FS81 §7.2, J p. 590: "`dμ_{I_β}` … as a vague limit of the
measures `dμ_{I_β,Ω}` … when `Ω ↗ ℤ²`"): along some sequence of radii `R_k → ∞`, the laws
`sosLiteralDiffLaw` in the boxes `[-R_k, R_k]²` (those containing `A`, all but finitely many)
converge to `ν` on every difference configuration `d : A → ℤ` (on the countable discrete space
`ℤ^A`, vague convergence is the convergence of the point masses). -/
def IsSOSLiteralLimit (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (A : Finset (ℤ × ℤ)) (w : ℤ × ℤ)
    (hw : w ∈ A) (ν : Measure (A → ℤ)) : Prop :=
  ∃ Rs : ℕ → ℕ, Tendsto Rs atTop atTop ∧ ∀ d : A → ℤ,
    Tendsto (fun k : {k : ℕ //
        A ⊆ Finset.Icc (-(Rs k : ℤ)) (Rs k) ×ˢ Finset.Icc (-(Rs k : ℤ)) (Rs k)} =>
      sosLiteralDiffLaw β hβ hβ1 A w hw (Rs k) k.2 {d}) atTop (𝓝 (ν {d}))

end FroehlichSpencer.BKT

end
