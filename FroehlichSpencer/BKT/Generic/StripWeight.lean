/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Strip weights (generic core, the shared weight interface)

The edge weight of FS81 §4 and §6–7 is an analytic interpolation `w` of a bond weight.

This module states them as three predicates; the instances
are theorems (Gaussian weight: `Generic/StripWeightScaling.lean`; Appendix B and C interpolations:
`Generic/Instances/*`).

* `IsStripWeight w W c`: `w` is real and positive on `ℝ`, analytic, even and conjugation-symmetric
  on the closed strip `|Im z| ≤ W`, satisfies the translation bound (4.10)(iii)/(c)
  `|w(t + iu)/w(t)| ≤ e^{c(u)}` for `|u| ≤ W`, and is bounded on the strip by a single integrable
  majorant `B(t)` that vanishes at infinity (the contour-end condition of FS81 Lemma 4.3).

The
  translation cost `c` is even with `c(0) = 0`.
* `HasLogDerivBounds w W M`: property (d) for `m = 1, 2`,
  `|(log w)^{(m)}(t + iu) − (log w)^{(m)}(t)| ≤ M(u)`.
* `HasCurvatureBound w κ`: the one-sided curvature bound of FS81 (6.28),
  `log w(t + s) ≥ log w(t) + (log w)'(t) s − κ s²` on the real axis.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex Filter Topology

/-- FS81 Condition (4.10) with the Appendix B/C property (c) and the contour-end majorant: a strip
weight of width `W` and translation cost `c`. -/
structure IsStripWeight (w : ℂ → ℂ) (W : ℝ) (c : ℝ → ℝ) : Prop where
  width_nonneg : 0 ≤ W
  ofReal_im : ∀ x : ℝ, (w x).im = 0
  ofReal_re_pos : ∀ x : ℝ, 0 < (w x).re
  analyticAt : ∀ z : ℂ, |z.im| ≤ W → AnalyticAt ℂ w z
  even : ∀ z : ℂ, |z.im| ≤ W → w (-z) = w z
  conj : ∀ z : ℂ, |z.im| ≤ W → (starRingEnd ℂ) (w z) = w ((starRingEnd ℂ) z)
  ratio_le : ∀ t u : ℝ, |u| ≤ W → ‖w ((t : ℂ) + (u : ℂ) * I) / w t‖ ≤ Real.exp (c u)
  bounded : ∃ M : ℝ, ∀ t u : ℝ, |u| ≤ W → ‖w ((t : ℂ) + (u : ℂ) * I)‖ ≤ M
  majorant : ∃ B : ℝ → ℝ, Integrable B ∧ Tendsto B (cocompact ℝ) (𝓝 0) ∧
    ∀ t u : ℝ, |u| ≤ W → ‖w ((t : ℂ) + (u : ℂ) * I)‖ ≤ B t
  cost_even : ∀ u, c (-u) = c u
  cost_zero : c 0 = 0

/-- FS81 Appendix B/C property (d), `m = 1, 2`. -/
structure HasLogDerivBounds (w : ℂ → ℂ) (W : ℝ) (M : ℝ → ℝ) : Prop where
  logDeriv_sub_le : ∀ t u : ℝ, |u| ≤ W →
    ‖logDeriv w ((t : ℂ) + (u : ℂ) * I) - logDeriv w t‖ ≤ M u
  deriv_logDeriv_sub_le : ∀ t u : ℝ, |u| ≤ W →
    ‖deriv (logDeriv w) ((t : ℂ) + (u : ℂ) * I) - deriv (logDeriv w) t‖ ≤ M u

/-- FS81 (6.28): the one-sided curvature bound `log w(t+s) ≥ log w(t) + (log w)'(t) s - κ s²`. -/
def HasCurvatureBound (w : ℂ → ℂ) (κ : ℝ) : Prop :=
  ∀ t s : ℝ, Real.log (w t).re + (logDeriv w t).re * s - κ * s ^ 2 ≤ Real.log (w ((t + s : ℝ) : ℂ)).re

namespace IsStripWeight

variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

/-- A strip weight does not vanish on the real axis. -/
theorem ofReal_ne_zero (hw : IsStripWeight w W c) (x : ℝ) : w x ≠ 0 := fun h =>
  (hw.ofReal_re_pos x).ne' (by rw [h, Complex.zero_re])

/-- On the real axis a strip weight is the real number `(w x).re`. -/
theorem ofReal_eq (hw : IsStripWeight w W c) (x : ℝ) : w x = ((w x).re : ℂ) :=
  Complex.ext (by simp) (by simp [hw.ofReal_im x])

end IsStripWeight

end FroehlichSpencer.BKT.Generic

end
