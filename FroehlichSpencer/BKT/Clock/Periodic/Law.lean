/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Periodic.ClockWeight
public import FroehlichSpencer.BKT.Generic.EdgeLaw.Defs
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The finite compact-angle clock reference law

After the rescaling `φ = n θ`, a finite set of sites carries product Lebesgue measure on the
fundamental interval `(-πn, πn]` and edge density `∏ exp (β cos (∇φ/n))`.

This module defines its
normalized law and proves that it is a probability measure.

The half-open interval is equivalent
to the paper's closed interval for integration.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Periodic

open MeasureTheory

/-- The half-open fundamental interval `(-πn, πn]` for the rescaled angle. -/
def clockAngleIoc (n : ℝ) : Set ℝ :=
  Set.Ioc (-clockAnglePeriod n / 2) (clockAnglePeriod n / 2)

/-- Product Lebesgue measure on the compact angle box with period `2πn`. -/
def compactAngleBaseMeasure {d : ℕ} (P : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => volume.restrict (Set.Ioc (-P / 2) (P / 2))

/-- Product Lebesgue measure on the compact angle box with period `2πn`. -/
def clockAngleBaseMeasure {d : ℕ} (n : ℝ) : Measure (Fin d → ℝ) :=
  compactAngleBaseMeasure (clockAnglePeriod n)

/-- The unnormalized finite-box edge density. -/
def clockBoxDensity {d : ℕ} (β n : ℝ) {E : Type*} [Fintype E]
    (G : Multigraph (Fin d) E) (φ : Fin d → ℝ) : ℝ :=
  ∏ e, (clockEdgeWeight β n ((G.grad φ e : ℝ) : ℂ)).re

/-- The finite unnormalized clock measure on the compact angle box. -/
def clockBoxMeasure {d : ℕ} (β n : ℝ) {E : Type*} [Fintype E]
    (G : Multigraph (Fin d) E) : Measure (Fin d → ℝ) :=
  clockAngleBaseMeasure n |>.withDensity fun φ => ENNReal.ofReal (clockBoxDensity β n G φ)

/-- The finite-volume partition function of the compact-angle law. -/
def clockBoxMass {d : ℕ} (β n : ℝ) {E : Type*} [Fintype E]
    (G : Multigraph (Fin d) E) : ENNReal := clockBoxMeasure β n G Set.univ

/-- The normalized finite compact-angle clock reference law. -/
def clockBoxLaw {d : ℕ} (β n : ℝ) {E : Type*} [Fintype E]
    (G : Multigraph (Fin d) E) : Measure (Fin d → ℝ) :=
  (clockBoxMass β n G)⁻¹ • clockBoxMeasure β n G

theorem measure_clockAngleBase_univ_ne_top {d : ℕ} {n : ℝ} :
    clockAngleBaseMeasure (d := d) n Set.univ ≠ ⊤ := by
  rw [clockAngleBaseMeasure, compactAngleBaseMeasure, Measure.pi_univ]
  apply ENNReal.prod_ne_top
  intro i hi
  rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

theorem measure_clockAngleBase_univ_ne_zero {d : ℕ} {n : ℝ} (hn : 0 < n) :
    clockAngleBaseMeasure (d := d) n Set.univ ≠ 0 := by
  rw [clockAngleBaseMeasure, compactAngleBaseMeasure, Measure.pi_univ]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  have hP : 0 < clockAnglePeriod n := by
    unfold clockAnglePeriod
    positivity
  have hlen : clockAnglePeriod n / 2 - -clockAnglePeriod n / 2 = clockAnglePeriod n := by ring
  rw [hlen]
  exact (ENNReal.ofReal_pos.mpr hP).ne'

theorem isFiniteMeasure_clockAngleBaseMeasure {d : ℕ} {n : ℝ} :
    IsFiniteMeasure (clockAngleBaseMeasure (d := d) n) := by
  refine ⟨?_⟩
  exact lt_top_iff_ne_top.mpr measure_clockAngleBase_univ_ne_top

theorem isFiniteMeasure_compactAngleBaseMeasure {d : ℕ} {P : ℝ} :
    IsFiniteMeasure (compactAngleBaseMeasure (d := d) P) := by
  refine ⟨lt_top_iff_ne_top.mpr ?_⟩
  rw [compactAngleBaseMeasure, Measure.pi_univ]
  apply ENNReal.prod_ne_top
  intro i hi
  rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

instance instIsFiniteMeasureCompactAngleBaseMeasure {d : ℕ} {P : ℝ} :
    IsFiniteMeasure (compactAngleBaseMeasure (d := d) P) :=
  isFiniteMeasure_compactAngleBaseMeasure

theorem measurable_clockBoxDensity {d : ℕ} (β n : ℝ) {E : Type*} [Fintype E]
    (G : Multigraph (Fin d) E) : Measurable (clockBoxDensity β n G) := by
  unfold clockBoxDensity
  refine (continuous_finsetProd _ fun e _ => ?_).measurable
  have hg : Continuous fun φ : Fin d → ℝ => G.grad φ e := by
    unfold Multigraph.grad
    fun_prop
  have hcont : Continuous fun φ : Fin d → ℝ =>
      Real.exp (β * Real.cos (G.grad φ e / n)) := by fun_prop
  have heq : (fun φ : Fin d → ℝ =>
      (clockEdgeWeight β n ((G.grad φ e : ℝ) : ℂ)).re) =
      fun φ => Real.exp (β * Real.cos (G.grad φ e / n)) := by
    funext φ
    rw [clockEdgeWeight_ofReal]
    rfl
  rw [heq]
  exact hcont

theorem clockBoxDensity_bounds {d : ℕ} {β n : ℝ} {E : Type*} [Fintype E]
    (G : Multigraph (Fin d) E) (hβ : 0 ≤ β) (φ : Fin d → ℝ) :
    Real.exp (-β) ^ Fintype.card E ≤ clockBoxDensity β n G φ ∧
      clockBoxDensity β n G φ ≤ Real.exp β ^ Fintype.card E := by
  have hprod : clockBoxDensity β n G φ =
      ∏ e, Real.exp (β * Real.cos (G.grad φ e / n)) := by
    unfold clockBoxDensity
    refine Finset.prod_congr rfl fun e he => ?_
    rw [clockEdgeWeight_ofReal]
    rfl
  constructor
  · rw [hprod]
    calc
      Real.exp (-β) ^ Fintype.card E = ∏ e : E, Real.exp (-β) := by simp
      _ ≤ ∏ e, Real.exp (β * Real.cos (G.grad φ e / n)) := by
        apply Finset.prod_le_prod₀
        · intro e he
          exact (Real.exp_pos _).le
        · intro e he
          apply Real.exp_le_exp.mpr
          have hc := Real.neg_one_le_cos (G.grad φ e / n)
          have hmul := mul_le_mul_of_nonneg_left hc hβ
          nlinarith
  · rw [hprod]
    calc
      ∏ e, Real.exp (β * Real.cos (G.grad φ e / n)) ≤ ∏ e : E, Real.exp β := by
        apply Finset.prod_le_prod₀
        · intro e he
          exact (Real.exp_pos _).le
        · intro e he
          apply Real.exp_le_exp.mpr
          have hc := Real.cos_le_one (G.grad φ e / n)
          have hmul := mul_le_mul_of_nonneg_left hc hβ
          nlinarith
      _ = Real.exp β ^ Fintype.card E := by simp

theorem clockBoxMass_eq_lintegral {d : ℕ} {β n : ℝ} {E : Type*} [Fintype E]
    (G : Multigraph (Fin d) E) :
    clockBoxMass β n G = ∫⁻ φ, ENNReal.ofReal (clockBoxDensity β n G φ)
      ∂clockAngleBaseMeasure n := by
  rw [clockBoxMass, clockBoxMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

theorem clockBoxMass_pos {d : ℕ} {β n : ℝ} {E : Type*} [Fintype E]
    (G : Multigraph (Fin d) E) (hβ : 0 ≤ β) (hn : 0 < n) :
    0 < clockBoxMass β n G := by
  rw [clockBoxMass_eq_lintegral]
  have hlower : ∀ φ, ENNReal.ofReal (Real.exp (-β) ^ Fintype.card E) ≤
      ENNReal.ofReal (clockBoxDensity β n G φ) := by
    intro φ
    exact ENNReal.ofReal_le_ofReal (clockBoxDensity_bounds G hβ φ).1
  have h := lintegral_mono (μ := clockAngleBaseMeasure n) hlower
  rw [lintegral_const] at h
  have hconst : 0 < ENNReal.ofReal (Real.exp (-β) ^ Fintype.card E) :=
    ENNReal.ofReal_pos.mpr (pow_pos (Real.exp_pos _) _)
  have hbase : 0 < clockAngleBaseMeasure (d := d) n Set.univ :=
    pos_iff_ne_zero.mpr (measure_clockAngleBase_univ_ne_zero hn)
  exact lt_of_lt_of_le (ENNReal.mul_pos hconst.ne' hbase.ne') h

theorem clockBoxMass_ne_top {d : ℕ} {β n : ℝ} {E : Type*} [Fintype E]
    (G : Multigraph (Fin d) E) (hβ : 0 ≤ β) :
    clockBoxMass β n G ≠ ⊤ := by
  rw [clockBoxMass_eq_lintegral]
  have hupper : ∀ φ, ENNReal.ofReal (clockBoxDensity β n G φ) ≤
      ENNReal.ofReal (Real.exp β ^ Fintype.card E) := by
    intro φ
    exact ENNReal.ofReal_le_ofReal (clockBoxDensity_bounds G hβ φ).2
  have h := lintegral_mono (μ := clockAngleBaseMeasure n) hupper
  rw [lintegral_const] at h
  apply ne_of_lt
  exact lt_of_le_of_lt h (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top)
    (lt_top_iff_ne_top.mpr measure_clockAngleBase_univ_ne_top))

theorem isProbabilityMeasure_clockBoxLaw {d : ℕ} {β n : ℝ} {E : Type*} [Fintype E]
    (G : Multigraph (Fin d) E) (hβ : 0 ≤ β) (hn : 0 < n) :
    IsProbabilityMeasure (clockBoxLaw β n G) := by
  refine ⟨?_⟩
  change (clockBoxMass β n G)⁻¹ * clockBoxMass β n G = 1
  exact ENNReal.inv_mul_cancel (clockBoxMass_pos G hβ hn).ne'
    (clockBoxMass_ne_top G hβ)

end FroehlichSpencer.BKT.Clock.Periodic

end
