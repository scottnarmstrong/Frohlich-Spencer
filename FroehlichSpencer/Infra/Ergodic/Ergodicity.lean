/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Ergodic.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function

/-!
# Ergodicity of the `ℤ^ν` shift on i.i.d. configurations

For `ν ≥ 1`, every measurable set which is almost surely invariant under all lattice shifts has
probability `0` or `1` under `productMeasure μ`, and every integrable almost surely invariant
function is almost surely equal to its mean. The proof shows that the shift is mixing, by
approximating sets with cylinder sets (which are independent of their far shifts), and then
uses the Mathlib ergodic theory for the single shift in the first coordinate direction.
-/

@[expose] public section

open MeasureTheory Set
open scoped symmDiff

namespace FroehlichSpencer.Infra

variable {ν : ℕ}

private theorem abs_measureReal_sub_le_symmDiff {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsFiniteMeasure P] {X Y : Set α} :
    |P.real X - P.real Y| ≤ P.real (X ∆ Y) := by
  have h1 : P.real X ≤ P.real Y + P.real (X ∆ Y) := by
    calc P.real X ≤ P.real (Y ∪ (X ∆ Y)) := by
          apply measureReal_mono _ (measure_ne_top _ _)
          intro x hx
          by_cases hy : x ∈ Y
          · exact Or.inl hy
          · exact Or.inr (Or.inl ⟨hx, hy⟩)
      _ ≤ _ := measureReal_union_le _ _
  have h2 : P.real Y ≤ P.real X + P.real (X ∆ Y) := by
    calc P.real Y ≤ P.real (X ∪ (X ∆ Y)) := by
          apply measureReal_mono _ (measure_ne_top _ _)
          intro x hx
          by_cases hy : x ∈ X
          · exact Or.inl hy
          · exact Or.inr (Or.inr ⟨hx, hy⟩)
      _ ≤ _ := measureReal_union_le _ _
  rw [abs_le]
  constructor <;> linarith only [h1, h2]

private theorem shift_preimage_symmDiff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : Fin ν → ℤ) {X Y : Set ((Fin ν → ℤ) → ℝ)} (hX : MeasurableSet X) (hY : MeasurableSet Y) :
    (productMeasure μ).real ((latticeShift a ⁻¹' X) ∆ (latticeShift a ⁻¹' Y)) =
      (productMeasure μ).real (X ∆ Y) := by
  rw [← Set.preimage_symmDiff]
  exact congrArg ENNReal.toReal
    ((measurePreserving_latticeShift μ a).measure_preimage (hX.symmDiff hY).nullMeasurableSet)

private theorem mem_cylinder_iff_of_eq (s : Finset (Fin ν → ℤ)) (S : Set (s → ℝ))
    {v w : (Fin ν → ℤ) → ℝ} (hvw : ∀ x ∈ s, v x = w x) :
    v ∈ cylinder s S ↔ w ∈ cylinder s S := by
  have : s.restrict v = s.restrict w := funext fun i => hvw i i.2
  simp only [mem_cylinder, this]

private theorem dependsOn_cylinder (s : Finset (Fin ν → ℤ)) (S : Set (s → ℝ))
    (hS : MeasurableSet S) :
    DependsOn (↑s : Set (Fin ν → ℤ)) (cylinder s S) :=
  dependsOn_of_measurable_of_invariant hS.cylinder fun _ _ hvw =>
    mem_cylinder_iff_of_eq s S hvw

private theorem dependsOn_preimage_shift (a : Fin ν → ℤ) (s : Finset (Fin ν → ℤ))
    (S : Set (s → ℝ)) (hS : MeasurableSet S) :
    DependsOn (↑(s.image (· + a)) : Set (Fin ν → ℤ)) (latticeShift a ⁻¹' cylinder s S) := by
  refine dependsOn_of_measurable_of_invariant
    ((measurable_latticeShift a) hS.cylinder) fun v w hvw => ?_
  exact mem_cylinder_iff_of_eq s S fun x hx =>
    hvw (x + a) (by simp only [Finset.coe_image, mem_image, Finset.mem_coe]; exact ⟨x, hx, rfl⟩)

/-- Approximate mixing estimate for a set `C` which is independent of its `a`-shift. -/
private theorem abs_sub_sq_le_of_indep (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {A C : Set ((Fin ν → ℤ) → ℝ)} (hA : MeasurableSet A) (hCm : MeasurableSet C)
    (a : Fin ν → ℤ) (hinv : latticeShift a ⁻¹' A =ᵐ[productMeasure μ] A)
    (hmix : (productMeasure μ).real (C ∩ latticeShift a ⁻¹' C) =
      (productMeasure μ).real C * (productMeasure μ).real C) :
    |(productMeasure μ).real A - (productMeasure μ).real A ^ 2| ≤
      4 * (productMeasure μ).real (C ∆ A) := by
  set P : Measure ((Fin ν → ℤ) → ℝ) := productMeasure μ with hP
  have hA1 : P.real (A ∩ latticeShift a ⁻¹' A) = P.real A := by
    have : A ∩ latticeShift a ⁻¹' A =ᵐ[P] A := by
      have h := Filter.EventuallyEqSet.inter (Filter.EventuallyEq.refl (ae P) A) hinv
      rwa [Set.inter_self] at h
    exact congrArg ENNReal.toReal (measure_congr this)
  have hd1 := abs_measureReal_sub_le_symmDiff P (X := C) (Y := A)
  have hd2 : P.real ((latticeShift a ⁻¹' C) ∆ (latticeShift a ⁻¹' A)) = P.real (C ∆ A) :=
    shift_preimage_symmDiff μ a hCm hA
  have hsub : (C ∩ latticeShift a ⁻¹' C) ∆ (A ∩ latticeShift a ⁻¹' A) ⊆
      (C ∆ A) ∪ ((latticeShift a ⁻¹' C) ∆ (latticeShift a ⁻¹' A)) := by
    intro x hx
    simp only [Set.mem_symmDiff, mem_inter_iff, mem_preimage, mem_union] at hx ⊢
    tauto
  have hd3 : |P.real (C ∩ latticeShift a ⁻¹' C) - P.real (A ∩ latticeShift a ⁻¹' A)| ≤
      2 * P.real (C ∆ A) := by
    refine (abs_measureReal_sub_le_symmDiff P).trans ?_
    calc _ ≤ P.real ((C ∆ A) ∪ ((latticeShift a ⁻¹' C) ∆ (latticeShift a ⁻¹' A))) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ P.real (C ∆ A) + P.real ((latticeShift a ⁻¹' C) ∆ (latticeShift a ⁻¹' A)) :=
          measureReal_union_le _ _
      _ = 2 * P.real (C ∆ A) := by rw [hd2]; ring
  rw [hmix, hA1] at hd3
  have hp1 : P.real C ≤ 1 := measureReal_le_one
  have hp2 : P.real A ≤ 1 := measureReal_le_one
  have hp3 : 0 ≤ P.real C := measureReal_nonneg
  have hp4 : 0 ≤ P.real A := measureReal_nonneg
  have hsq : |P.real C * P.real C - P.real A ^ 2| ≤ 2 * |P.real C - P.real A| := by
    have : P.real C * P.real C - P.real A ^ 2 =
        (P.real C - P.real A) * (P.real C + P.real A) := by ring
    rw [this, abs_mul]
    have : |P.real C + P.real A| ≤ 2 := by
      rw [abs_of_nonneg (add_nonneg hp3 hp4)]; linarith only [hp1, hp2]
    calc _ ≤ |P.real C - P.real A| * 2 := by gcongr
      _ = _ := by ring
  rw [abs_le] at hd3 hsq hd1 ⊢
  have hd1' := abs_le.2 hd1
  constructor <;> linarith only [hd3, hsq, hd1']

/-- Approximate mixing estimate for a cylinder whose base is disjoint from its `a`-shift. -/
private theorem abs_sub_sq_le_of_cylinder (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {A : Set ((Fin ν → ℤ) → ℝ)} (hA : MeasurableSet A) (a : Fin ν → ℤ)
    (hinv : latticeShift a ⁻¹' A =ᵐ[productMeasure μ] A)
    (s : Finset (Fin ν → ℤ)) (S : Set (s → ℝ)) (hS : MeasurableSet S)
    (hdisj : Disjoint (↑s : Set (Fin ν → ℤ)) ↑(s.image (· + a))) :
    |(productMeasure μ).real A - (productMeasure μ).real A ^ 2| ≤
      4 * (productMeasure μ).real (cylinder s S ∆ A) := by
  refine abs_sub_sq_le_of_indep μ hA hS.cylinder a hinv ?_
  have h1 := measure_inter_eq_mul_of_dependsOn μ hdisj (dependsOn_cylinder s S hS)
    (dependsOn_preimage_shift a s S hS)
  have h2 : productMeasure μ (latticeShift a ⁻¹' cylinder s S) =
      productMeasure μ (cylinder s S) :=
    (measurePreserving_latticeShift μ a).measure_preimage hS.cylinder.nullMeasurableSet
  rw [Measure.real, h1, h2, ENNReal.toReal_mul]
  rfl

/-- The unit shift in the first coordinate direction, used as the generating shift. -/
private def unitShift (hν : 0 < ν) (N : ℕ) : Fin ν → ℤ := Pi.single ⟨0, hν⟩ (N : ℤ)

private theorem exists_far_shift (hν : 0 < ν) (s : Finset (Fin ν → ℤ)) :
    ∃ N : ℕ, Disjoint (↑s : Set (Fin ν → ℤ)) ↑(s.image (· + unitShift hν N)) := by
  set M : ℕ := ∑ x ∈ s, (x ⟨0, hν⟩).natAbs with hM
  have hle : ∀ x ∈ s, (x ⟨0, hν⟩).natAbs ≤ M := fun x hx =>
    Finset.single_le_sum (f := fun x => (x ⟨0, hν⟩).natAbs) (fun _ _ => Nat.zero_le _) hx
  refine ⟨2 * M + 1, ?_⟩
  rw [Set.disjoint_left]
  intro y hy hy'
  simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hy hy'
  obtain ⟨x, hx, rfl⟩ := hy'
  have h1 := hle x hx
  have h2 := hle _ hy
  have h3 : (x + unitShift hν (2 * M + 1)) ⟨0, hν⟩ = x ⟨0, hν⟩ + ((2 * M + 1 : ℕ) : ℤ) := by
    simp [unitShift]
  rw [h3] at h2
  omega

private theorem sq_eq_of_invariant (hν : 0 < ν) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {A : Set ((Fin ν → ℤ) → ℝ)} (hA : MeasurableSet A)
    (hinv : ∀ N : ℕ, latticeShift (unitShift hν N) ⁻¹' A =ᵐ[productMeasure μ] A) :
    (productMeasure μ).real A = (productMeasure μ).real A ^ 2 := by
  have key : ∀ δ : ℝ, 0 < δ →
      |(productMeasure μ).real A - (productMeasure μ).real A ^ 2| ≤ 4 * δ := by
    intro δ hδ
    obtain ⟨C, hC, hCA⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := productMeasure μ) (C := measurableCylinders fun _ : Fin ν → ℤ => ℝ)
      isSetRing_measurableCylinders
      ⟨{Set.univ}, by simp,
        by simpa using univ_mem_measurableCylinders (fun _ : Fin ν → ℤ => ℝ), by simp⟩
      generateFrom_measurableCylinders.symm hA (ENNReal.ofReal_pos.2 hδ)
    obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders C).1 hC
    obtain ⟨N, hN⟩ := exists_far_shift hν s
    have := abs_sub_sq_le_of_cylinder μ hA _ (hinv N) s S hS hN
    have hlt : (productMeasure μ).real (cylinder s S ∆ A) ≤ δ := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hCA.le
      rwa [ENNReal.toReal_ofReal hδ.le] at this
    linarith only [this, hlt]
  have h0 : |(productMeasure μ).real A - (productMeasure μ).real A ^ 2| ≤ 0 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := key (δ / 4) (by positivity)
    linarith only [this]
  have := abs_nonpos_iff.1 h0
  linarith only [this]

private theorem measure_eq_zero_or_one_aux (hν : 0 < ν) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {A : Set ((Fin ν → ℤ) → ℝ)} (hA : MeasurableSet A)
    (hinv : ∀ N : ℕ, latticeShift (unitShift hν N) ⁻¹' A =ᵐ[productMeasure μ] A) :
    productMeasure μ A = 0 ∨ productMeasure μ A = 1 := by
  have h := sq_eq_of_invariant hν μ hA hinv
  have h' : (productMeasure μ).real A = 0 ∨ (productMeasure μ).real A = 1 := by
    have : (productMeasure μ).real A * ((productMeasure μ).real A - 1) = 0 := by
      linear_combination -h
    rcases mul_eq_zero.1 this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by linarith only [h1])
  rcases h' with h1 | h1
  · left
    exact (ENNReal.toReal_eq_zero_iff _).1 h1 |>.resolve_right (measure_ne_top _ _)
  · right
    rw [← ENNReal.ofReal_toReal (measure_ne_top (productMeasure μ) A)]
    simpa [Measure.real] using congrArg ENNReal.ofReal h1

/-- Almost surely shift-invariant measurable sets have probability `0` or `1`. -/
theorem measure_eq_zero_or_one_of_invariant (hν : 0 < ν) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {A : Set ((Fin ν → ℤ) → ℝ)} (hA : MeasurableSet A)
    (hinv : ∀ a, latticeShift a ⁻¹' A =ᵐ[productMeasure μ] A) :
    productMeasure μ A = 0 ∨ productMeasure μ A = 1 :=
  measure_eq_zero_or_one_aux hν μ hA fun _ => hinv _

private theorem latticeShift_unitShift_succ (hν : 0 < ν) (N : ℕ) (v : (Fin ν → ℤ) → ℝ) :
    latticeShift (unitShift hν (N + 1)) v =
      latticeShift (unitShift hν 1) (latticeShift (unitShift hν N) v) := by
  rw [latticeShift_latticeShift]
  congr 1
  simp only [unitShift, Nat.cast_add, Nat.cast_one]
  rw [← Pi.single_add, add_comm]

private theorem preimage_unitShift_eq (hν : 0 < ν) {A : Set ((Fin ν → ℤ) → ℝ)}
    (hA : latticeShift (unitShift hν 1) ⁻¹' A = A) (N : ℕ) :
    latticeShift (unitShift hν N) ⁻¹' A = A := by
  induction N with
  | zero =>
    have : unitShift hν 0 = 0 := by simp [unitShift]
    rw [this]; ext v; simp
  | succ N ih =>
    have : latticeShift (unitShift hν (N + 1)) ⁻¹' A =
        latticeShift (unitShift hν N) ⁻¹' (latticeShift (unitShift hν 1) ⁻¹' A) := by
      ext v
      simp only [mem_preimage]
      rw [latticeShift_unitShift_succ]
    rw [this, hA, ih]

private theorem ergodic_unitShift (hν : 0 < ν) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Ergodic (latticeShift (unitShift hν 1)) (productMeasure μ) := by
  refine ⟨measurePreserving_latticeShift μ _, ⟨fun A hA hAinv => ?_⟩⟩
  have := measure_eq_zero_or_one_aux hν μ hA fun N => by
    rw [preimage_unitShift_eq hν hAinv N]
  rcases this with h | h
  · exact Filter.eventuallyEmptyOrUniv_iff'.2 (Or.inl (ae_eq_empty.2 h))
  · refine Filter.eventuallyEmptyOrUniv_iff'.2 (Or.inr (ae_eq_univ.2 ?_))
    rw [prob_compl_eq_zero_iff hA, h]

/-- The unit shift in the first coordinate direction is ergodic for every i.i.d. product measure
(`ν ≥ 1`), in the sense of Mathlib's `Ergodic`. -/
theorem ergodic_latticeShift_single (hν : 0 < ν) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Ergodic (latticeShift (Pi.single ⟨0, hν⟩ 1)) (productMeasure μ) := by
  have h := ergodic_unitShift hν μ
  have e : unitShift hν 1 = Pi.single ⟨0, hν⟩ 1 := by simp [unitShift]
  rwa [e] at h

/-- Almost surely shift-invariant integrable functions are almost surely equal to their mean. -/
theorem ae_eq_integral_of_invariant (hν : 0 < ν) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Integrable f (productMeasure μ))
    (hinv : ∀ a, f ∘ latticeShift a =ᵐ[productMeasure μ] f) :
    f =ᵐ[productMeasure μ] fun _ => ∫ v, f v ∂productMeasure μ := by
  obtain ⟨c, hc⟩ := (ergodic_unitShift hν μ).ae_eq_const_of_ae_eq_comp_ae
    hf.aestronglyMeasurable (hinv _)
  have : ∫ v, f v ∂productMeasure μ = c := by
    rw [integral_congr_ae hc]
    simp
  rw [this]
  exact hc

end FroehlichSpencer.Infra
