/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# real angles in `[-π, π)` and the unit circle

The literal perimeter surface integrates over real link angles `θ ∈ [-π, π)` with Lebesgue measure
(FS82 (2.1)–(2.3)).

This module is the change of variables:
`t = θ / (2π)` maps the product of the restricted Lebesgue measures to `(2π)^n` times the product
Haar measure, also after a reindexing of the coordinates.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.PrimalInterface

open MeasureTheory

local instance circleScaling_factOne : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

/-- The point of the unit additive circle with physical angle `t`: the class of `t / (2π)`. -/
noncomputable def angleToCircle (t : ℝ) : UnitAddCircle := ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)

theorem continuous_angleToCircle : Continuous angleToCircle :=
  (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_id.div_const _)

theorem measurable_angleToCircle : Measurable angleToCircle :=
  continuous_angleToCircle.measurable

/-- Lebesgue measure on `[-π, π)` is mapped to `2π` times the Haar probability measure. -/
theorem map_angleToCircle :
    Measure.map angleToCircle ((volume : Measure ℝ).restrict (Set.Ico (-Real.pi) Real.pi)) =
      ENNReal.ofReal (2 * Real.pi) • (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hf : Measurable (fun t : ℝ => t * (2 * Real.pi)⁻¹) := measurable_id.mul_const _
  have hIco : (volume : Measure ℝ).restrict (Set.Ico (-Real.pi) Real.pi) =
      volume.restrict (Set.Ioc (-Real.pi) Real.pi) :=
    Measure.restrict_congr_set Ico_ae_eq_Ioc
  have hpre : (fun t : ℝ => t * (2 * Real.pi)⁻¹) ⁻¹' Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) =
      Set.Ioc (-Real.pi) Real.pi := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioc]
    rw [← div_eq_mul_inv, lt_div_iff₀ hpi, div_le_iff₀ hpi]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hscale : Measure.map (fun t : ℝ => t * (2 * Real.pi)⁻¹)
      ((volume : Measure ℝ).restrict (Set.Ioc (-Real.pi) Real.pi)) =
        ENNReal.ofReal (2 * Real.pi) •
          (volume : Measure ℝ).restrict (Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) := by
    rw [← hpre, ← Measure.restrict_map hf measurableSet_Ioc,
      Real.map_volume_mul_right (inv_ne_zero hpi.ne'), Measure.restrict_smul, inv_inv,
      abs_of_pos hpi]
  have hmk := (AddCircle.measurePreserving_mk (1 : ℝ) (-1 / 2 : ℝ)).map_eq
  have hvol : (AddCircle.measureSpace (1 : ℝ)).volume = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  have hcomp : angleToCircle =
      (fun x : ℝ => (x : UnitAddCircle)) ∘ fun t : ℝ => t * (2 * Real.pi)⁻¹ := by
    funext t
    simp [angleToCircle, div_eq_mul_inv]
  rw [hIco, hcomp, ← Measure.map_map (AddCircle.measurable_mk' (a := (1 : ℝ))) hf, hscale,
    Measure.map_smul, hmk, hvol]
  exact (AddCircle.measurable_mk' (a := (1 : ℝ))).aemeasurable

/-- The product form, with a reindexing of the coordinates. -/
theorem map_pi_angleToCircle {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    Measure.map (fun (θ : ι → ℝ) (j : κ) => angleToCircle (θ (e.symm j)))
        (Measure.pi fun _ : ι => (volume : Measure ℝ).restrict (Set.Ico (-Real.pi) Real.pi)) =
      ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι •
        Measure.pi fun _ : κ => (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hc0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero, not_le] using hpi
  have hctop : ENNReal.ofReal (2 * Real.pi) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hn0 : ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ hc0
  have hntop : ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι ≠ ⊤ := ENNReal.pow_ne_top hctop
  have hG : Measurable fun (θ : ι → ℝ) (j : κ) => angleToCircle (θ (e.symm j)) :=
    measurable_pi_iff.mpr fun j => measurable_angleToCircle.comp (measurable_pi_apply _)
  have key : (ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι)⁻¹ •
      Measure.map (fun (θ : ι → ℝ) (j : κ) => angleToCircle (θ (e.symm j)))
        (Measure.pi fun _ : ι => (volume : Measure ℝ).restrict (Set.Ico (-Real.pi) Real.pi)) =
      Measure.pi fun _ : κ => (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    have hpre : (fun (θ : ι → ℝ) (j : κ) => angleToCircle (θ (e.symm j))) ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ fun i : ι => angleToCircle ⁻¹' s (e i) := by
      ext θ
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · intro h i
        simpa using h (e i)
      · intro h j
        simpa using h (e.symm j)
    have h1 : ∀ i : ι, ((volume : Measure ℝ).restrict (Set.Ico (-Real.pi) Real.pi))
        (angleToCircle ⁻¹' s (e i)) =
          ENNReal.ofReal (2 * Real.pi) * AddCircle.haarAddCircle (s (e i)) := fun i => by
      rw [← Measure.map_apply measurable_angleToCircle (hs _), map_angleToCircle,
        Measure.smul_apply, smul_eq_mul]
    rw [Measure.smul_apply, Measure.map_apply hG (MeasurableSet.univ_pi hs), hpre, Measure.pi_pi]
    simp_rw [h1]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hn0 hntop, one_mul]
    exact Equiv.prod_comp e fun j => AddCircle.haarAddCircle (s j)
  rw [← key, smul_smul, ENNReal.mul_inv_cancel hn0 hntop, one_smul]

/-- The character of the circle at the point of angle `t`. -/
theorem fourier_one_angleToCircle (t : ℝ) :
    fourier (T := (1 : ℝ)) 1 (angleToCircle t) = Complex.exp (Complex.I * (t : ℂ)) := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  rw [angleToCircle, fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- Integer combinations of angles. -/
theorem angleToCircle_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ) (t : ι → ℝ) :
    ∑ i ∈ s, a i • angleToCircle (t i) = angleToCircle (∑ i ∈ s, (a i : ℝ) * t i) := by
  unfold angleToCircle
  rw [Finset.sum_div]
  change _ = (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
    (∑ i ∈ s, (a i : ℝ) * t i / (2 * Real.pi))
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change a i • ((t i / (2 * Real.pi) : ℝ) : UnitAddCircle) =
    (((a i : ℝ) * t i / (2 * Real.pi) : ℝ) : UnitAddCircle)
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_div_assoc]

end FroehlichSpencer.FS82.PrimalInterface

end
