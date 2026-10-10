/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.PrimalInterface.CircleScaling
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# a normalized density on real angles and its circle form

For a continuous positive density `D` on the torus `κ → UnitAddCircle`, the probability measure on
real angle configurations `θ : ι → ℝ` with density `D (θ / 2π)` with respect to the product of the
Lebesgue measures on `[-π, π)`, divided by its total mass, integrates a function `F (θ / 2π)` to
`∫ D F / ∫ D` with respect to the Haar probability measure of the torus.

The factor `(2π)^n`
cancels.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.PrimalInterface

open MeasureTheory

local instance normalizedLaw_factOne : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

variable {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)

/-- The circle configuration of a real angle configuration, with the coordinates reindexed. -/
noncomputable def circleConfig (θ : ι → ℝ) : κ → UnitAddCircle :=
  fun j => angleToCircle (θ (e.symm j))

omit [Fintype ι] [Fintype κ] in
theorem measurable_circleConfig : Measurable (circleConfig e) :=
  measurable_pi_iff.mpr fun _ => measurable_angleToCircle.comp (measurable_pi_apply _)

/-- The product of the Lebesgue measures on `[-π, π)`. -/
noncomputable abbrev angleBase (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => (volume : Measure ℝ).restrict (Set.Ico (-Real.pi) Real.pi)

/-- The Haar probability measure of the torus. -/
noncomputable abbrev torusHaar (κ : Type*) [Fintype κ] : Measure (κ → UnitAddCircle) :=
  Measure.pi fun _ : κ => (AddCircle.haarAddCircle : Measure UnitAddCircle)

theorem map_circleConfig :
    Measure.map (circleConfig e) (angleBase ι) =
      ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι • torusHaar κ :=
  map_pi_angleToCircle e

theorem integrable_of_continuous_torus {F : Type*} [NormedAddCommGroup F]
    (g : (κ → UnitAddCircle) → F) (hg : Continuous g) : Integrable g (torusHaar κ) := by
  apply MeasureTheory.integrableOn_univ.mp
  exact hg.continuousOn.integrableOn_compact isCompact_univ

/-- The total mass of the unnormalized law. -/
theorem withDensity_circleConfig_univ (D : (κ → UnitAddCircle) → ℝ) (hD : Continuous D)
    (hD0 : ∀ z, 0 ≤ D z) :
    ((angleBase ι).withDensity fun θ => ENNReal.ofReal (D (circleConfig e θ))) Set.univ =
      ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
        ENNReal.ofReal (∫ z, D z ∂torusHaar κ) := by
  have hmeas : Measurable fun z : κ → UnitAddCircle => ENNReal.ofReal (D z) :=
    ENNReal.measurable_ofReal.comp hD.measurable
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← lintegral_map hmeas (measurable_circleConfig e), map_circleConfig, lintegral_smul_measure,
    smul_eq_mul,
    ofReal_integral_eq_lintegral_ofReal (integrable_of_continuous_torus D hD)
      (Filter.Eventually.of_forall hD0)]

/-- Integrals against the unnormalized law. -/
theorem integral_withDensity_circleConfig (D : (κ → UnitAddCircle) → ℝ) (hD : Continuous D)
    (hD0 : ∀ z, 0 ≤ D z) (F : (κ → UnitAddCircle) → ℂ) (hF : Continuous F) :
    ∫ θ, F (circleConfig e θ)
        ∂((angleBase ι).withDensity fun θ => ENNReal.ofReal (D (circleConfig e θ))) =
      (ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι).toReal •
        ∫ z, (D z : ℂ) * F z ∂torusHaar κ := by
  have hρ : Measurable fun θ : ι → ℝ => ENNReal.ofReal (D (circleConfig e θ)) :=
    ENNReal.measurable_ofReal.comp (hD.measurable.comp (measurable_circleConfig e))
  have hcont : Continuous fun z : κ → UnitAddCircle => (D z : ℂ) * F z :=
    (Complex.continuous_ofReal.comp hD).mul hF
  rw [integral_withDensity_eq_integral_toReal_smul hρ
    (Filter.Eventually.of_forall fun θ => ENNReal.ofReal_lt_top)]
  have h1 : (fun θ : ι → ℝ =>
        (ENNReal.ofReal (D (circleConfig e θ))).toReal • F (circleConfig e θ)) =
      fun θ => (fun z : κ → UnitAddCircle => (D z : ℂ) * F z) (circleConfig e θ) := by
    funext θ
    rw [ENNReal.toReal_ofReal (hD0 _), Complex.real_smul]
  rw [h1, ← integral_map (measurable_circleConfig e).aemeasurable hcont.aestronglyMeasurable,
    map_circleConfig, integral_smul_measure]

/-- The normalized law is a probability measure. -/
theorem isProbabilityMeasure_normalized (D : (κ → UnitAddCircle) → ℝ) (hD : Continuous D)
    (hD0 : ∀ z, 0 ≤ D z) (hZ : 0 < ∫ z, D z ∂torusHaar κ) :
    IsProbabilityMeasure
      ((((angleBase ι).withDensity fun θ => ENNReal.ofReal (D (circleConfig e θ))) Set.univ)⁻¹ •
        ((angleBase ι).withDensity fun θ => ENNReal.ofReal (D (circleConfig e θ)))) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hc0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero, not_le] using hpi
  have hZ0 : ENNReal.ofReal (∫ z, D z ∂torusHaar κ) ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero, not_le] using hZ
  refine ⟨?_⟩
  rw [Measure.smul_apply, smul_eq_mul, withDensity_circleConfig_univ e D hD hD0]
  exact ENNReal.inv_mul_cancel (mul_ne_zero (pow_ne_zero _ hc0) hZ0)
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)

/-- Expectations in the normalized law are ratios of Haar integrals. -/
theorem integral_normalized (D : (κ → UnitAddCircle) → ℝ) (hD : Continuous D)
    (hD0 : ∀ z, 0 ≤ D z) (hZ : 0 < ∫ z, D z ∂torusHaar κ)
    (F : (κ → UnitAddCircle) → ℂ) (hF : Continuous F) :
    ∫ θ, F (circleConfig e θ)
        ∂((((angleBase ι).withDensity fun θ => ENNReal.ofReal (D (circleConfig e θ))) Set.univ)⁻¹ •
          ((angleBase ι).withDensity fun θ => ENNReal.ofReal (D (circleConfig e θ)))) =
      (∫ z, (D z : ℂ) * F z ∂torusHaar κ) / ((∫ z, D z ∂torusHaar κ : ℝ) : ℂ) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have ha : 0 < (ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι).toReal := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hpi.le]
    positivity
  rw [integral_smul_measure, integral_withDensity_circleConfig e D hD hD0 F hF,
    withDensity_circleConfig_univ e D hD hD0, ENNReal.toReal_inv, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hZ.le, smul_smul, Complex.real_smul]
  have hscal : ((ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι).toReal *
      ∫ z, D z ∂torusHaar κ)⁻¹ * (ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι).toReal =
        (∫ z, D z ∂torusHaar κ)⁻¹ := by
    field_simp
  rw [hscal, Complex.ofReal_inv, div_eq_inv_mul]

end FroehlichSpencer.FS82.PrimalInterface

end
