/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-! # FS81's analytic interpolation of `e^{-β|n|}` (Appendix C) -/

open Real

@[expose] public section

namespace FroehlichSpencer.BKT

/-- FS81's interpolation `I_β` of `n ↦ e^{-β|n|}` (Appendix C, (C.1), J p. 599), on the real axis,
for `β > 0`: `I_β(t) = L_β(t) E_β(t)` with `L_β(t) = exp[-β^{2/3}(1 + β^{2/3} t²)^{1/2}]` and
`E_β(t) = exp[-∑_{n ∈ ℤ} (β|n| - β^{2/3}(1 + β^{2/3} n²)^{1/2}) sin²[(t - n)π]/((t - n)²π²)]`, the
quotient `sin²[sπ]/(s²π²)` being `sinc(πs)²` (value `1` at `s = 0`). This is the interpolation of
FS81's state (7.16), with the printed condition (d) replaced by the weaker derivative bound proved in
`SOS/Interp`. The definition is (C.1) as printed. -/
noncomputable def sosInterpolation (β : ℝ) (_hβ : 0 < β) (t : ℝ) : ℝ :=
  Real.exp (-(β ^ (2 / 3 : ℝ)) * Real.sqrt (1 + β ^ (2 / 3 : ℝ) * t ^ 2)) *
    Real.exp (-∑' n : ℤ,
      (β * |(n : ℝ)| - β ^ (2 / 3 : ℝ) * Real.sqrt (1 + β ^ (2 / 3 : ℝ) * (n : ℝ) ^ 2)) *
        Real.sinc (π * (t - n)) ^ 2)

end FroehlichSpencer.BKT

end
