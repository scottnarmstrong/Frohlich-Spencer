/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.GridOffsetLaw
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

/-!
# Torus translations of the compact clock box

The compact box `(−πn, πn]^V` is a fundamental domain of the torus `(ℝ / 2πnℤ)^V`. A real site
shift `σ`, followed by reduction into the box, preserves the box measure. Hence the box integral
of an integrand periodic in each site coordinate is invariant under `φ ↦ φ + σ`. This is the change
of variables that moves the seam profile from the bond product onto the Fejér multiplier.

* `measurePreserving_toIocMod_add`: the scalar statement, through `AddCircle`;
* `integral_gridBoxMeasure_add_periodic`: the box statement.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open MeasureTheory
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact

/-- Translation followed by reduction into `(−P/2, P/2]` preserves Lebesgue measure on that
interval. -/
theorem measurePreserving_toIocMod_add {P : ℝ} (hP : 0 < P) (t : ℝ) :
    MeasurePreserving (fun x : ℝ => toIocMod hP (-P / 2) (x + t))
      (volume.restrict (Set.Ioc (-P / 2) (P / 2)))
      (volume.restrict (Set.Ioc (-P / 2) (P / 2))) := by
  have : Fact (0 < P) := ⟨hP⟩
  have hI : Set.Ioc (-P / 2) (P / 2) = Set.Ioc (-P / 2) (-P / 2 + P) := by
    congr 1
    ring
  rw [hI]
  have h1 := AddCircle.measurePreserving_mk P (-P / 2)
  have h2 : MeasurePreserving (fun y : AddCircle P => y + (t : AddCircle P)) volume volume :=
    measurePreserving_add_right volume (t : AddCircle P)
  have h3 := AddCircle.measurePreserving_equivIoc P (a := -P / 2)
  have h4 : MeasurePreserving (Subtype.val : Set.Ioc (-P / 2) (-P / 2 + P) → ℝ)
      (Measure.comap Subtype.val volume) (volume.restrict (Set.Ioc (-P / 2) (-P / 2 + P))) :=
    ⟨measurable_subtype_coe, map_comap_subtype_coe measurableSet_Ioc _⟩
  have hcomp := h4.comp (h3.comp (h2.comp h1))
  convert hcomp using 1
  funext x
  simp only [Function.comp_apply]
  rw [← AddCircle.coe_add, AddCircle.equivIoc, QuotientAddGroup.equivIocMod_coe]

variable {V : Type} [Fintype V]

/-- **Torus translation on the compact box.** The box integral of a continuous integrand that is
periodic under integer multiples of the period `2πn` in each site coordinate is invariant under
every real site shift. -/
theorem integral_gridBoxMeasure_add_periodic {n : ℝ} (hn : 0 < n) (g : (V → ℝ) → ℝ)
    (hg : Continuous g)
    (hper : ∀ (φ : V → ℝ) (m : V → ℤ),
      g (φ + fun v => (m v : ℝ) * clockAnglePeriod n) = g φ)
    (σ : V → ℝ) :
    ∫ φ, g (φ + σ) ∂gridBoxMeasure n V = ∫ φ, g φ ∂gridBoxMeasure n V := by
  rw [integral_gridBoxMeasure, integral_gridBoxMeasure]
  set P := clockAnglePeriod n with hPdef
  have hP : 0 < P := by
    rw [hPdef, clockAnglePeriod]
    positivity
  let e := siteEquiv V
  let τ : Fin (Fintype.card V) → ℝ := fun j => σ (e.symm j)
  let W : (Fin (Fintype.card V) → ℝ) → (Fin (Fintype.card V) → ℝ) :=
    fun φ j => toIocMod hP (-P / 2) (φ j + τ j)
  have hW : MeasurePreserving W (clockAngleBaseMeasure n) (clockAngleBaseMeasure n) := by
    unfold clockAngleBaseMeasure compactAngleBaseMeasure
    exact measurePreserving_pi _ _ fun j => measurePreserving_toIocMod_add hP (τ j)
  have hpull : Measurable (pullField V) := measurableEmbedding_pullField.measurable
  have hshift : ∀ φ : Fin (Fintype.card V) → ℝ,
      g (pullField V φ + σ) = g (pullField V (W φ)) := by
    intro φ
    let m : V → ℤ := fun v => -toIocDiv hP (-P / 2) (φ (e v) + τ (e v))
    have hfield : pullField V (W φ) = (pullField V φ + σ) + fun v => (m v : ℝ) * P := by
      funext v
      simp only [pullField, W, m, τ, Pi.add_apply]
      rw [← self_sub_toIocDiv_zsmul hP, zsmul_eq_mul]
      change φ (e v) + σ (e.symm (e v)) - _ * P = φ (e v) + σ v + _
      rw [Equiv.symm_apply_apply]
      push_cast
      ring
    rw [hfield, hper]
  calc
    ∫ φ, g (pullField V φ + σ) ∂clockAngleBaseMeasure n =
        ∫ φ, g (pullField V (W φ)) ∂clockAngleBaseMeasure n :=
      integral_congr_ae (Filter.Eventually.of_forall hshift)
    _ = ∫ φ, g (pullField V φ) ∂Measure.map W (clockAngleBaseMeasure n) :=
      (integral_map hW.measurable.aemeasurable
        (hg.measurable.comp hpull).aestronglyMeasurable).symm
    _ = ∫ φ, g (pullField V φ) ∂clockAngleBaseMeasure n := by rw [hW.map_eq]

end FroehlichSpencer.BKT.Clock.Disorder

end
