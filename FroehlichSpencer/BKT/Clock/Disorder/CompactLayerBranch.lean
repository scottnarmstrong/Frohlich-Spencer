/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.CompactLowerBranch
public import FroehlichSpencer.BKT.Clock.Compact.RealFactor
import Mathlib.Tactic

/-!
# Even compact charge-layer branch

A neutral compact charge layer at zero shift gives a nonnegative multiplier invariant under field
inversion. The compact curvature lemma therefore supplies the full edge-density lower bound for
that multiplier. The remaining T1.5 step is the comparison from this multiplier to the shifted
layer product.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open MeasureTheory
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Clock.Periodic

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- The unshifted real local-factor product of one compact clock charge ensemble. -/
def compactClockLayerMultiplier (β n : ℝ) (G : Multigraph V E)
    (R : Finset (V → ℤ)) (z : (V → ℤ) → ℝ) (a : (V → ℤ) → V → ℝ)
    (φ : V → ℝ) : ℝ :=
  ∏ ϱ ∈ R, (1 + z ϱ * clockF β n (gradLinear G (a ϱ)) (gradLinear G φ)
    (∑ j, φ j * (ϱ j : ℝ)))

/-- A bond-offset clock density, before normalization by its partition function. -/
def compactClockLayerOffsetDensity (β n : ℝ) (G : Multigraph V E) (θ : E → ℝ)
    (φ : V → ℝ) : ℝ :=
  ∏ e, Real.exp (β * Real.cos ((G.grad φ e + θ e) / n))

private theorem compactClockLayerFactor_pos {β n : ℝ} (hβ : 0 ≤ β) (hn : 0 < n)
    (b x : E → ℝ) (θ z : ℝ) (hz : |z| ≤ 1 / 8) :
    0 < 1 + z * clockF β n b x θ := by
  have hF := abs_clockF_le_one hβ hn b x θ
  have hprod : |z * clockF β n b x θ| ≤ 1 / 8 := by
    rw [abs_mul]
    calc
      |z| * |clockF β n b x θ| ≤ (1 / 8) * 1 :=
        mul_le_mul hz hF (abs_nonneg _) (by norm_num)
      _ = 1 / 8 := by norm_num
  linarith [neg_abs_le (z * clockF β n b x θ)]

omit [DecidableEq V] in
/-- The unshifted compact charge-layer multiplier is nonnegative when all activities are small. -/
theorem compactClockLayerMultiplier_nonneg {β n : ℝ} (hβ : 0 ≤ β) (hn : 0 < n)
    (G : Multigraph V E) (R : Finset (V → ℤ)) (z : (V → ℤ) → ℝ)
    (a : (V → ℤ) → V → ℝ) (hz : ∀ ϱ ∈ R, |z ϱ| ≤ 1 / 8) (φ : V → ℝ) :
    0 ≤ compactClockLayerMultiplier β n G R z a φ := by
  unfold compactClockLayerMultiplier
  exact Finset.prod_nonneg fun ϱ hϱ =>
    (compactClockLayerFactor_pos hβ hn (gradLinear G (a ϱ)) (gradLinear G φ)
      (∑ j, φ j * (ϱ j : ℝ)) (z ϱ) (hz ϱ hϱ)).le

omit [DecidableEq V] in
/-- The unshifted compact charge-layer multiplier is even under field inversion. -/
theorem compactClockLayerMultiplier_neg {β n : ℝ} (hβ : 0 ≤ β) (hn : 0 < n)
    (G : Multigraph V E) (R : Finset (V → ℤ)) (z : (V → ℤ) → ℝ)
    (a : (V → ℤ) → V → ℝ) (φ : V → ℝ) :
    compactClockLayerMultiplier β n G R z a (-φ) =
      compactClockLayerMultiplier β n G R z a φ := by
  unfold compactClockLayerMultiplier
  refine Finset.prod_congr rfl fun ϱ hϱ => ?_
  have hw := clockEdgeWeight_isCompactPeriodicWeight hβ hn
  let b := gradLinear G (a ϱ)
  let x := gradLinear G φ
  let s := ∑ j, φ j * (ϱ j : ℝ)
  have hW : ∀ e, |b e| ≤ ∑ e, |b e| := fun e =>
    Finset.single_le_sum (f := fun e => |b e|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ e)
  have hF := hw.localFactor_neg b x (hW) s
  have hgrad : gradLinear G (-φ) = -gradLinear G φ := by
    rw [map_neg]
  have hsum : ∑ j, (-φ) j * (ϱ j : ℝ) = -∑ j, φ j * (ϱ j : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp [Pi.neg_apply]
  change 1 + z ϱ *
      (localFactor (clockEdgeWeight β n) (clockShiftCost β n)
        (gradLinear G (a ϱ)) (gradLinear G (-φ))
        (∑ j, (-φ) j * (ϱ j : ℝ))).re = _
  rw [hgrad, hsum]
  have hlocal := hw.localFactor_neg b x hW s
  have hreal := congrArg Complex.re hlocal
  simpa [b, x, s, clockF] using congrArg (fun t : ℝ => 1 + z ϱ * t) hreal

omit [DecidableEq V] in
/-- Absolute bound for the unshifted compact charge-layer multiplier. -/
theorem abs_compactClockLayerMultiplier_le {β n : ℝ} (hβ : 0 ≤ β) (hn : 0 < n)
    (G : Multigraph V E) (R : Finset (V → ℤ)) (z : (V → ℤ) → ℝ)
    (a : (V → ℤ) → V → ℝ) (hz : ∀ ϱ ∈ R, |z ϱ| ≤ 1 / 8) (φ : V → ℝ) :
    |compactClockLayerMultiplier β n G R z a φ| ≤ (9 / 8 : ℝ) ^ R.card := by
  unfold compactClockLayerMultiplier
  rw [Finset.abs_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun ϱ hϱ => ?_
  have hF := abs_clockF_le_one hβ hn (gradLinear G (a ϱ)) (gradLinear G φ)
    (∑ j, φ j * (ϱ j : ℝ))
  calc
    |1 + z ϱ * clockF β n (gradLinear G (a ϱ)) (gradLinear G φ)
        (∑ j, φ j * (ϱ j : ℝ))| ≤
          |(1 : ℝ)| + |z ϱ * clockF β n (gradLinear G (a ϱ)) (gradLinear G φ)
            (∑ j, φ j * (ϱ j : ℝ))| := abs_add_le _ _
    _ = 1 + |z ϱ * clockF β n (gradLinear G (a ϱ)) (gradLinear G φ)
        (∑ j, φ j * (ϱ j : ℝ))| := by rw [abs_one]
    _ ≤ 1 + 1 / 8 := by
      have hmul : |z ϱ * clockF β n (gradLinear G (a ϱ)) (gradLinear G φ)
          (∑ j, φ j * (ϱ j : ℝ))| ≤ 1 / 8 := by
        rw [abs_mul]
        calc
          |z ϱ| * |clockF β n (gradLinear G (a ϱ)) (gradLinear G φ)
              (∑ j, φ j * (ϱ j : ℝ))| ≤ (1 / 8) * 1 :=
            mul_le_mul (hz ϱ hϱ) hF (abs_nonneg _) (by norm_num)
          _ = 1 / 8 := by norm_num
      linarith
    _ = 9 / 8 := by norm_num

/-- The compact curvature estimate applies to a zero-shift charge-layer multiplier. This is the
edge-density part of the compact T1.5 lower branch. -/
theorem integral_compactClockLayer_offset_lower_of_negInvariant
    {β n κ : ℝ} (hβ : 0 ≤ β) (hn : 0 < n)
    (μ : Measure (V → ℝ))
    (hneg : MeasurePreserving (fun φ : V → ℝ => -φ) μ μ)
    (G : Multigraph V E) (R : Finset (V → ℤ)) (z : (V → ℤ) → ℝ)
    (a : (V → ℤ) → V → ℝ) (hz : ∀ ϱ ∈ R, |z ϱ| ≤ 1 / 8)
    (hcurv : HasCurvatureBound (clockEdgeWeight β n) κ) (θ : E → ℝ)
    (hbase : Integrable (fun φ => clockDensity β n G φ *
      compactClockLayerMultiplier β n G R z a φ) μ)
    (hoff : Integrable (fun φ => compactClockLayerOffsetDensity β n G θ φ *
      compactClockLayerMultiplier β n G R z a φ) μ) :
    Real.exp (-κ * ∑ e, θ e ^ 2) *
        ∫ φ, clockDensity β n G φ * compactClockLayerMultiplier β n G R z a φ ∂μ ≤
      ∫ φ, compactClockLayerOffsetDensity β n G θ φ *
        compactClockLayerMultiplier β n G R z a φ ∂μ := by
  exact integral_clockDensity_shift_lower_of_negInvariant μ hneg G hcurv θ
    (compactClockLayerMultiplier β n G R z a)
    (compactClockLayerMultiplier_nonneg hβ hn G R z a hz)
    (fun φ => compactClockLayerMultiplier_neg hβ hn G R z a φ)
    hbase hoff

end FroehlichSpencer.BKT.Clock.Disorder

end
