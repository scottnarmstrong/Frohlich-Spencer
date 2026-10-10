/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Moment.RealShift
public import FroehlichSpencer.BKT.Clock.Compact.FejerLimit
public import FroehlichSpencer.BKT.Clock.Periodic.ClockWeight
import Mathlib.Tactic

/-!
# Compact-measure symmetrization for the lower branch

The T1.5 lower branch uses inversion symmetry to cancel its odd first-order exponent. This version
isolates that argument for any finite measure preserved by field inversion, including the compact
clock carrier once its symmetry is supplied.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open MeasureTheory
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Clock.Periodic

/-- Negation preserves the compact product box measure. The endpoint convention only changes a
null boundary; each scalar factor is mapped to the same half-open interval. -/
theorem measurePreserving_neg_compactAngleBaseMeasure {d : ℕ} {P : ℝ} :
    MeasurePreserving (fun φ : Fin d → ℝ => -φ)
      (compactAngleBaseMeasure P) (compactAngleBaseMeasure P) := by
  let a := P / 2
  let μ : Measure ℝ := volume.restrict (Set.Ioc (-a) a)
  have hpre : Neg.neg ⁻¹' Set.Ioc (-a) a = Set.Ico (-a) a := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_Ico]
    constructor <;> intro h <;> constructor <;> linarith
  have hae : Set.Ioc (-a) a =ᵐ[volume] Set.Ico (-a) a :=
    Ioc_ae_eq_Icc.trans Ico_ae_eq_Icc.symm
  have hset : volume.restrict (Set.Ioc (-a) a) = volume.restrict (Set.Ico (-a) a) :=
    Measure.restrict_congr_set hae
  have hmap : Measure.map Neg.neg (volume.restrict (Set.Ico (-a) a)) =
      volume.restrict (Set.Ioc (-a) a) := by
    have h := measurableEmbedding_neg.restrict_map (μ := volume) (s := Set.Ioc (-a) a)
    rw [Measure.map_neg_eq_self] at h
    rw [hpre] at h
    exact h.symm
  have hscalar : MeasurePreserving Neg.neg μ μ := by
    refine ⟨measurable_neg, ?_⟩
    change Measure.map Neg.neg (volume.restrict (Set.Ioc (-a) a)) =
      volume.restrict (Set.Ioc (-a) a)
    calc
      _ = Measure.map Neg.neg (volume.restrict (Set.Ico (-a) a)) :=
        congrArg (Measure.map Neg.neg) hset
      _ = volume.restrict (Set.Ioc (-a) a) := hmap
  have hinterval : Set.Ioc (-P / 2) (P / 2) = Set.Ioc (-a) a := by
    congr 1
    dsimp [a]
    ring
  have hscalar' : MeasurePreserving Neg.neg
      (volume.restrict (Set.Ioc (-P / 2) (P / 2)))
      (volume.restrict (Set.Ioc (-P / 2) (P / 2))) := by
    simpa only [hinterval] using hscalar
  unfold compactAngleBaseMeasure
  have hpi := measurePreserving_pi (fun _ : Fin d =>
      volume.restrict (Set.Ioc (-P / 2) (P / 2)))
    (fun _ => volume.restrict (Set.Ioc (-P / 2) (P / 2)))
    (f := fun _ => Neg.neg) (fun _ => hscalar')
  change MeasurePreserving (fun φ : Fin d → ℝ => fun i => -φ i)
    (Measure.pi fun _ : Fin d => volume.restrict (Set.Ioc (-P / 2) (P / 2)))
    (Measure.pi fun _ : Fin d => volume.restrict (Set.Ioc (-P / 2) (P / 2)))
  exact hpi

/-- The rescaled compact clock reference box is invariant under field inversion. -/
theorem measurePreserving_neg_clockAngleBaseMeasure {d : ℕ} (n : ℝ) :
    MeasurePreserving (fun φ : Fin d → ℝ => -φ)
      (clockAngleBaseMeasure n) (clockAngleBaseMeasure n) := by
  unfold clockAngleBaseMeasure
  exact measurePreserving_neg_compactAngleBaseMeasure

variable {V E : Type} [Fintype V] [Fintype E]

/-- The first-order exponent in the real shift of the compact clock edge product. -/
def compactClockShiftExponent (G : Multigraph V E) (β n : ℝ) (θ : E → ℝ)
    (φ : V → ℝ) : ℝ :=
  ∑ e, (logDeriv (clockEdgeWeight β n) ((G.grad φ e : ℝ) : ℂ)).re * θ e

private theorem clockLogDeriv_real_part (β n t : ℝ) :
    (logDeriv (clockEdgeWeight β n) (t : ℂ)).re = -β / n * Real.sin (t / n) := by
  rw [clockEdgeWeight_logDeriv]
  have harg : (t : ℂ) / n = (↑(t / n) : ℂ) := by
    push_cast
    simp [div_eq_mul_inv]
  have hcoeff : -((β : ℂ) / n) = ((-β / n : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_sin, hcoeff, ← Complex.ofReal_mul]
  simp only [Complex.ofReal_re]

omit [Fintype V] in
/-- The clock shift exponent is odd in the field. -/
theorem compactClockShiftExponent_neg (G : Multigraph V E) (β n : ℝ) (θ : E → ℝ)
    (φ : V → ℝ) :
    compactClockShiftExponent G β n θ (-φ) = -compactClockShiftExponent G β n θ φ := by
  unfold compactClockShiftExponent
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hg : G.grad (-φ) e = -G.grad φ e := by
    simp only [Multigraph.grad, Pi.neg_apply]
    ring
  rw [hg, clockLogDeriv_real_part, clockLogDeriv_real_part]
  rw [show -G.grad φ e / n = -(G.grad φ e / n) by ring, Real.sin_neg]
  ring

omit [Fintype V] in
/-- The unshifted compact clock edge density is even under field inversion. -/
theorem clockDensity_neg (β n : ℝ) (G : Multigraph V E) (φ : V → ℝ) :
    clockDensity β n G (-φ) = clockDensity β n G φ := by
  unfold clockDensity
  refine Finset.prod_congr rfl fun e _ => ?_
  have hg : G.grad (-φ) e = -G.grad φ e := by
    simp only [Multigraph.grad, Pi.neg_apply]
    ring
  rw [hg, neg_div, Real.cos_neg]

omit [Fintype V] in
/-- The compact clock's unnormalized bond product has the standard T1.5 edge-shift lower bound.
The local first-order term is retained explicitly; inversion symmetry cancels it after integration. -/
theorem clockDensity_shift_lower (G : Multigraph V E) {β n κ : ℝ}
    (hκ : HasCurvatureBound (clockEdgeWeight β n) κ) (φ : V → ℝ) (θ : E → ℝ) :
    clockDensity β n G φ * Real.exp
      (compactClockShiftExponent G β n θ φ - κ * ∑ e, θ e ^ 2) ≤
      ∏ e, Real.exp (β * Real.cos ((G.grad φ e + θ e) / n)) := by
  have hedge (e : E) :
      β * Real.cos (G.grad φ e / n) +
          (logDeriv (clockEdgeWeight β n) ((G.grad φ e : ℝ) : ℂ)).re * θ e -
            κ * θ e ^ 2 ≤ β * Real.cos ((G.grad φ e + θ e) / n) := by
    have h := hκ (G.grad φ e) (θ e)
    rw [clockEdgeWeight_ofReal, clockEdgeWeight_ofReal] at h
    simp only [Complex.ofReal_re, Real.log_exp] at h
    exact h
  unfold clockDensity compactClockShiftExponent
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsum :
      (∑ e, (β * Real.cos (G.grad φ e / n) +
        (logDeriv (clockEdgeWeight β n) ((G.grad φ e : ℝ) : ℂ)).re * θ e -
          κ * θ e ^ 2)) ≤
      ∑ e, β * Real.cos ((G.grad φ e + θ e) / n) :=
    Finset.sum_le_sum fun e _ => hedge e
  have harg :
      (∑ e, β * Real.cos (G.grad φ e / n)) +
          ((∑ e, (logDeriv (clockEdgeWeight β n) ((G.grad φ e : ℝ) : ℂ)).re * θ e) -
            κ * ∑ e, θ e ^ 2) =
        ∑ e, (β * Real.cos (G.grad φ e / n) +
          (logDeriv (clockEdgeWeight β n) ((G.grad φ e : ℝ) : ℂ)).re * θ e -
            κ * θ e ^ 2) := by
    simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [harg]
  exact hsum

/-- Odd-exponent symmetrization for a finite measure preserved by field inversion. -/
theorem integral_ge_of_odd_exponent_of_negInvariant
    {V : Type*} [Fintype V] [DecidableEq V]
    {μ : Measure (V → ℝ)} {I f H : (V → ℝ) → ℝ}
    (R : ℝ) (hneg : MeasurePreserving (fun φ : V → ℝ => -φ) μ μ)
    (hI : Integrable I μ) (hf : Integrable f μ) (hf0 : ∀ φ, 0 ≤ f φ)
    (hfeven : ∀ᵐ φ ∂μ, f (-φ) = f φ)
    (hHodd : ∀ φ, H (-φ) = -H φ)
    (hle : ∀ φ, Real.exp (-R) * (f φ * Real.exp (H φ)) ≤ I φ) :
    Real.exp (-R) * ∫ φ, f φ ∂μ ≤ ∫ φ, I φ ∂μ := by
  have hIneg : Integrable (fun φ => I (-φ)) μ :=
    (hneg.integrable_comp_emb (Homeomorph.neg (V → ℝ)).measurableEmbedding).mpr hI
  have hsym : ∫ φ, I φ ∂μ = (1 / 2 : ℝ) * ∫ φ, (I φ + I (-φ)) ∂μ := by
    rw [integral_add hI hIneg, hneg.integral_comp (Homeomorph.neg (V → ℝ)).measurableEmbedding I]
    ring
  rw [hsym, ← integral_const_mul, ← integral_const_mul]
  refine integral_mono_ae (hf.const_mul _) ((hI.add hIneg).const_mul _) ?_
  filter_upwards [hfeven] with φ hφ
  have h1 := hle φ
  have h2 := hle (-φ)
  rw [hφ, hHodd φ] at h2
  have hcosh : 2 ≤ Real.exp (H φ) + Real.exp (-H φ) := by
    linarith [Real.add_one_le_exp (H φ), Real.add_one_le_exp (-H φ)]
  have hRpos := Real.exp_pos (-R)
  have hf0φ := hf0 φ
  show Real.exp (-R) * f φ ≤ 1 / 2 * (I φ + I (-φ))
  nlinarith [mul_le_mul_of_nonneg_left hcosh (mul_nonneg hRpos.le hf0φ)]

/-- The edge-shift lower bound after inversion symmetrization, for any even nonnegative
multiplier. This is the compact clock analogue of the edge-density part of the T1.5 branch. -/
theorem integral_clockDensity_shift_lower_of_negInvariant [DecidableEq V]
    (μ : Measure (V → ℝ))
    (hneg : MeasurePreserving (fun φ : V → ℝ => -φ) μ μ)
    (G : Multigraph V E) {β n κ : ℝ}
    (hκ : HasCurvatureBound (clockEdgeWeight β n) κ) (θ : E → ℝ)
    (g : (V → ℝ) → ℝ) (hg0 : ∀ φ, 0 ≤ g φ) (hgeven : ∀ φ, g (-φ) = g φ)
    (hbase : Integrable (fun φ => clockDensity β n G φ * g φ) μ)
    (hshift : Integrable (fun φ =>
      (∏ e, Real.exp (β * Real.cos ((G.grad φ e + θ e) / n))) * g φ) μ) :
    Real.exp (-κ * ∑ e, θ e ^ 2) *
        ∫ φ, clockDensity β n G φ * g φ ∂μ ≤
      ∫ φ, (∏ e, Real.exp (β * Real.cos ((G.grad φ e + θ e) / n))) * g φ ∂μ := by
  have hle (φ : V → ℝ) :
      Real.exp (-(κ * ∑ e, θ e ^ 2)) *
          ((clockDensity β n G φ * g φ) *
            Real.exp (compactClockShiftExponent G β n θ φ)) ≤
        (∏ e, Real.exp (β * Real.cos ((G.grad φ e + θ e) / n))) * g φ := by
    have hpt := clockDensity_shift_lower G hκ φ θ
    rw [show Real.exp (-(κ * ∑ e, θ e ^ 2)) *
        ((clockDensity β n G φ * g φ) *
          Real.exp (compactClockShiftExponent G β n θ φ)) =
        (clockDensity β n G φ * Real.exp
          (compactClockShiftExponent G β n θ φ - κ * ∑ e, θ e ^ 2)) * g φ by
            rw [show compactClockShiftExponent G β n θ φ - κ * ∑ e, θ e ^ 2 =
              compactClockShiftExponent G β n θ φ + -(κ * ∑ e, θ e ^ 2) by ring,
              Real.exp_add]
            ring]
    exact mul_le_mul_of_nonneg_right hpt (hg0 φ)
  simpa only [neg_mul] using
    (FroehlichSpencer.BKT.Clock.Disorder.integral_ge_of_odd_exponent_of_negInvariant
      (κ * ∑ e, θ e ^ 2) hneg hshift hbase
      (fun φ => mul_nonneg (clockDensity_pos β n G φ).le (hg0 φ))
      (Filter.Eventually.of_forall fun φ => by
        rw [clockDensity_neg, hgeven])
      (compactClockShiftExponent_neg G β n θ) hle)


end FroehlichSpencer.BKT.Clock.Disorder

end
