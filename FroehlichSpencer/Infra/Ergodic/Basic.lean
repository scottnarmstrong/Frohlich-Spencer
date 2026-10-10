/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.ProductMeasure
public import Mathlib.Data.Pi.Interval

/-!
# Lattice shifts, cubes and cube averages on `ℤ^ν`

The shift action of `ℤ^ν` on configurations `v : ℤ^ν → ℝ`, `latticeShift a v = fun x => v (x + a)`,
the cubes `cube ν L = [-L, L]^ν ∩ ℤ^ν` and the cube averages
`cubeAverage f L v = |cube ν L|⁻¹ ∑_{a ∈ cube ν L} f (latticeShift a v)`.

The shift preserves every
i.i.d. product measure.

Motivation: the ergodic theorem behind the integrated density of states of
Fröhlich–Spencer (1983), (1.10), Fröhlich–Spencer (1983); nothing here is model specific.
-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.Infra

variable {ν : ℕ}

/-- The shift of a configuration by `a ∈ ℤ^ν`: `latticeShift a v x = v (x + a)`. -/
def latticeShift (a : Fin ν → ℤ) (v : (Fin ν → ℤ) → ℝ) : (Fin ν → ℤ) → ℝ :=
  fun x => v (x + a)

/-- The cube `[-L, L]^ν ∩ ℤ^ν`. -/
def cube (ν L : ℕ) : Finset (Fin ν → ℤ) :=
  Finset.Icc (fun _ => -(L : ℤ)) (fun _ => (L : ℤ))

/-- The average of `f` over the shifts of `v` by the points of the cube of side `2L + 1`. -/
noncomputable def cubeAverage (f : ((Fin ν → ℤ) → ℝ) → ℝ) (L : ℕ)
    (v : (Fin ν → ℤ) → ℝ) : ℝ :=
  ((cube ν L).card : ℝ)⁻¹ * ∑ a ∈ cube ν L, f (latticeShift a v)

theorem latticeShift_apply (a : Fin ν → ℤ) (v : (Fin ν → ℤ) → ℝ) (x : Fin ν → ℤ) :
    latticeShift a v x = v (x + a) := rfl

@[simp] theorem latticeShift_zero (v : (Fin ν → ℤ) → ℝ) : latticeShift 0 v = v := by
  funext x; simp [latticeShift]

theorem latticeShift_latticeShift (a b : Fin ν → ℤ) (v : (Fin ν → ℤ) → ℝ) :
    latticeShift a (latticeShift b v) = latticeShift (a + b) v := by
  funext x; simp [latticeShift, add_assoc]

theorem mem_cube {L : ℕ} {x : Fin ν → ℤ} : x ∈ cube ν L ↔ ∀ i, -(L : ℤ) ≤ x i ∧ x i ≤ L := by
  simp [cube, Pi.le_def, forall_and]

theorem card_cube (ν L : ℕ) : (cube ν L).card = (2 * L + 1) ^ ν := by
  rw [cube, Pi.card_Icc]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem card_cube_pos (ν L : ℕ) : 0 < (cube ν L).card := by
  rw [card_cube]; positivity

theorem cube_mono {L L' : ℕ} (h : L ≤ L') : cube ν L ⊆ cube ν L' := by
  intro x hx
  rw [mem_cube] at hx ⊢
  intro i
  have := hx i
  constructor <;> omega

theorem measurable_latticeShift (a : Fin ν → ℤ) : Measurable (latticeShift (ν := ν) a) :=
  Measurable.of_eval fun x => measurable_pi_apply (x + a)

/-- The shift preserves every i.i.d. product measure. -/
theorem measurePreserving_latticeShift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : Fin ν → ℤ) :
    MeasurePreserving (latticeShift a) (productMeasure μ) (productMeasure μ) := by
  refine ⟨measurable_latticeShift a, ?_⟩
  have h := Measure.infinitePi_map_piCongrLeft (fun _ : Fin ν → ℤ => μ) (Equiv.subRight a)
  have e : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin ν → ℤ => ℝ) (Equiv.subRight a)) :
      ((Fin ν → ℤ) → ℝ) → (Fin ν → ℤ) → ℝ) = latticeShift a := by
    funext v x
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, latticeShift]
  rw [← e]
  exact h

theorem cubeAverage_const (c : ℝ) (L : ℕ) (v : (Fin ν → ℤ) → ℝ) :
    cubeAverage (fun _ => c) L v = c := by
  have h := card_cube_pos ν L
  simp only [cubeAverage, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The shift is a measurable embedding (its inverse is the shift by `-a`). -/
theorem measurableEmbedding_latticeShift (a : Fin ν → ℤ) :
    MeasurableEmbedding (latticeShift (ν := ν) a) := by
  refine MeasurableEmbedding.of_measurable_inverse (g := latticeShift (-a))
    (measurable_latticeShift a) ?_ (measurable_latticeShift (-a)) ?_
  · have : Set.range (latticeShift (ν := ν) a) = Set.univ := by
      refine Set.eq_univ_of_forall fun v => ⟨latticeShift (-a) v, ?_⟩
      rw [latticeShift_latticeShift, add_neg_cancel, latticeShift_zero]
    rw [this]; exact MeasurableSet.univ
  · intro v
    rw [latticeShift_latticeShift, neg_add_cancel, latticeShift_zero]

theorem integral_comp_latticeShift (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : Fin ν → ℤ)
    (f : ((Fin ν → ℤ) → ℝ) → ℝ) :
    ∫ v, f (latticeShift a v) ∂productMeasure μ = ∫ v, f v ∂productMeasure μ :=
  (measurePreserving_latticeShift μ a).integral_comp (measurableEmbedding_latticeShift a) f

theorem measurable_cubeAverage {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Measurable f) (L : ℕ) :
    Measurable (cubeAverage f L) :=
  measurable_const.mul (Finset.measurable_sum _ fun a _ => hf.comp (measurable_latticeShift a))

theorem integral_cubeAverage (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Integrable f (productMeasure μ)) (L : ℕ) :
    ∫ v, cubeAverage f L v ∂productMeasure μ = ∫ v, f v ∂productMeasure μ := by
  have h := card_cube_pos ν L
  have hi : ∀ a, Integrable (fun v => f (latticeShift a v)) (productMeasure μ) := fun a =>
    (measurePreserving_latticeShift μ a).integrable_comp_of_integrable hf
  simp only [cubeAverage]
  rw [integral_const_mul, integral_finsetSum _ fun a _ => hi a]
  simp only [integral_comp_latticeShift, Finset.sum_const, nsmul_eq_mul]
  field_simp

end FroehlichSpencer.Infra
