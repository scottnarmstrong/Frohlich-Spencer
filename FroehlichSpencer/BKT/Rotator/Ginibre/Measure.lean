/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.CurrentIntegration
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Restriction and reflection of the raw angle measure

Two measure-theoretic facts about the raw product measure on `[-π, π)^V`: restricting a
configuration along an injective site map pushes the measure forward to a constant multiple of the
smaller raw measure (the free sites are integrated out), and the measure is invariant under the
global reflection `θ ↦ -θ`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Ginibre

instance isFiniteMeasure_rotatorRawAngleMeasure (V : Type*) [Fintype V] [DecidableEq V] :
    IsFiniteMeasure (rotatorRawAngleMeasure V) := by
  have : IsFiniteMeasure (volume.restrict (Ico (-π) π)) :=
    ⟨by simp [Real.volume_Ico]⟩
  unfold rotatorRawAngleMeasure
  infer_instance

/-- Restricting the angles along an injective site map pushes the raw angle measure forward to
`(2π)^{|W| - |V|}` times the raw angle measure on the smaller site set. -/
theorem map_comp_rotatorRawAngleMeasure {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {ι : V → W} (hι : Function.Injective ι) :
    (rotatorRawAngleMeasure W).map (fun θ : W → ℝ => θ ∘ ι) =
      ENNReal.ofReal (2 * π) ^ (Fintype.card W - Fintype.card V) • rotatorRawAngleMeasure V := by
  classical
  have hν : (volume.restrict (Ico (-π) π)) univ = ENNReal.ofReal (2 * π) := by
    rw [Measure.restrict_apply_univ, Real.volume_Ico]
    congr 1
    ring
  set c : ENNReal := ENNReal.ofReal (2 * π) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; simp [Real.pi_pos]
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  set k := Fintype.card W - Fintype.card V with hk
  have hmeas : Measurable (fun θ : W → ℝ => θ ∘ ι) := by fun_prop
  have key : rotatorRawAngleMeasure V =
      (c ^ k)⁻¹ • (rotatorRawAngleMeasure W).map (fun θ : W → ℝ => θ ∘ ι) := by
    unfold rotatorRawAngleMeasure
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
    have hpre : (fun θ : W → ℝ => θ ∘ ι) ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (Function.extend ι s (fun _ => Set.univ)) := by
      ext θ
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply]
      constructor
      · intro h w
        by_cases hw : ∃ i, ι i = w
        · obtain ⟨i, rfl⟩ := hw
          rw [hι.extend_apply]
          exact h i
        · rw [Function.extend_apply' _ _ _ hw]
          exact Set.mem_univ _
      · intro h i
        have := h (ι i)
        rwa [hι.extend_apply] at this
    rw [hpre, Measure.pi_pi]
    have hsplit := Finset.prod_mul_prod_compl (Finset.univ.image ι)
      (fun w => (volume.restrict (Ico (-π) π)) (Function.extend ι s (fun _ => Set.univ) w))
    rw [← hsplit, Finset.prod_image (fun a _ b _ h => hι h)]
    have h1 : ∏ i : V, (volume.restrict (Ico (-π) π)) (Function.extend ι s (fun _ => Set.univ) (ι i))
        = ∏ i : V, (volume.restrict (Ico (-π) π)) (s i) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hι.extend_apply]
    have h2 : ∏ w ∈ (Finset.univ.image ι)ᶜ,
        (volume.restrict (Ico (-π) π)) (Function.extend ι s (fun _ => Set.univ) w) = c ^ k := by
      have : ∀ w ∈ (Finset.univ.image ι)ᶜ,
          (volume.restrict (Ico (-π) π)) (Function.extend ι s (fun _ => Set.univ) w) = c := by
        intro w hw
        have hw' : ¬ ∃ i, ι i = w := by
          simpa using hw
        rw [Function.extend_apply' _ _ _ hw', hν]
      rw [Finset.prod_congr rfl this, Finset.prod_const, Finset.card_compl,
        Finset.card_image_of_injective _ hι, Finset.card_univ]
    rw [h1, h2]
    simp only [smul_eq_mul]
    rw [mul_comm _ (c ^ k), ← mul_assoc, ENNReal.inv_mul_cancel (pow_ne_zero _ hc0)
      (ENNReal.pow_ne_top hct), one_mul]
  rw [key, smul_smul, ENNReal.mul_inv_cancel (pow_ne_zero _ hc0) (ENNReal.pow_ne_top hct), one_smul]

/-- Integrating a function of the restricted angles. -/
theorem integral_comp_rotatorRawAngleMeasure {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] {ι : V → W} (hι : Function.Injective ι) {f : (V → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (rotatorRawAngleMeasure V)) :
    ∫ θ : W → ℝ, f (θ ∘ ι) ∂rotatorRawAngleMeasure W =
      (2 * π) ^ (Fintype.card W - Fintype.card V) * ∫ θ : V → ℝ, f θ ∂rotatorRawAngleMeasure V := by
  have hmeas : Measurable (fun θ : W → ℝ => θ ∘ ι) := by fun_prop
  rw [← integral_map hmeas.aemeasurable (f := f)]
  · rw [map_comp_rotatorRawAngleMeasure hι, integral_smul_measure, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity [Real.pi_pos]), smul_eq_mul]
  · rw [map_comp_rotatorRawAngleMeasure hι]
    exact hf.smul_measure _

/-- The raw angle measure is invariant under the global reflection `θ ↦ -θ`. -/
theorem map_neg_rotatorRawAngleMeasure (V : Type*) [Fintype V] [DecidableEq V] :
    (rotatorRawAngleMeasure V).map (fun θ : V → ℝ => -θ) = rotatorRawAngleMeasure V := by
  have hν : (volume.restrict (Ico (-π) π)).map (fun t : ℝ => -t) =
      volume.restrict (Ico (-π) π) := by
    have h1 := Measure.restrict_map (μ := (volume : Measure ℝ)) (f := fun t : ℝ => -t)
      measurable_neg (measurableSet_Ioc (a := -π) (b := π))
    rw [Measure.map_neg_eq_self (volume : Measure ℝ), Set.neg_preimage, Set.neg_Ioc, neg_neg] at h1
    rw [← h1]
    exact Measure.restrict_congr_set Ico_ae_eq_Ioc.symm
  have h2 := Measure.pi_map_pi (μ := fun _ : V => volume.restrict (Ico (-π) π))
    (f := fun _ t => -t) (fun _ => measurable_neg.aemeasurable)
  simp only [hν] at h2
  exact h2

/-- Integrals against the raw angle measure are invariant under the global reflection. -/
theorem integral_neg_rotatorRawAngleMeasure (V : Type*) [Fintype V] [DecidableEq V]
    (f : (V → ℝ) → ℝ) :
    ∫ θ : V → ℝ, f (-θ) ∂rotatorRawAngleMeasure V = ∫ θ : V → ℝ, f θ ∂rotatorRawAngleMeasure V := by
  have hme : MeasurePreserving (MeasurableEquiv.neg (V → ℝ)) (rotatorRawAngleMeasure V)
      (rotatorRawAngleMeasure V) :=
    ⟨measurable_neg, map_neg_rotatorRawAngleMeasure V⟩
  exact hme.integral_comp' f

end FroehlichSpencer.BKT.Rotator.Ginibre

end
