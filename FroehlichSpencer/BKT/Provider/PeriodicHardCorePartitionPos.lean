/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.HardCoreSecondMoment
public import FroehlichSpencer.BKT.Surface.PeriodicHardCorePartition
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.periodicHardCorePartition_pos`

This module contains `FroehlichSpencer.BKT.Provider.periodicHardCorePartition_pos`, the proof of the
statement `FroehlichSpencer.BKT.periodicHardCorePartition_pos` (file
`FroehlichSpencer/BKT/Surface/PeriodicHardCorePartitionPos.lean`).

-/

@[expose] public section

open MeasureTheory Filter Topology
open Fin.CommRing
open FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMoment

noncomputable section

namespace FroehlichSpencer.BKT.Provider

theorem periodicHardCorePartition_pos (β : ℝ) (hβ : 0 < β) (z : ℝ) (Λ : Finset (ℤ × ℤ))
    (L : ℕ) (hL : 1 < L) : 0 < periodicHardCorePartition β hβ z Λ L hL := by
  have : NeZero L := ⟨by omega⟩
  set μ := gffLaw (squarePeriodic L) (squarePeriodic_connected L hL) β⁻¹ (inv_pos.mpr hβ) 0
  have hμ : IsProbabilityMeasure μ := isProbabilityMeasure_gffLaw _ _ _ _ _
  set red : Λ → Fin L × Fin L := fun x => ((x.1.1 : Fin L), (x.1.2 : Fin L))
  -- the charge pushed to the torus
  let push : (Λ → ℤ) → Fin L × Fin L → ℤ := fun q j => ∑ x, if red x = j then q x else 0
  have hpush : ∀ (q : Λ → ℤ) (φ : Fin L × Fin L → ℝ),
      ∑ x, φ (red x) * (q x : ℝ) = ∑ j, φ j * (push q j : ℝ) := by
    intro q φ
    simp only [push, Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hpushsum : ∀ q : Λ → ℤ, ∑ j, push q j = ∑ x, q x := by
    intro q
    simp only [push]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hexp : ∀ φ : Fin L × Fin L → ℝ,
      ∏ x ∈ Λ, (1 + z * Real.cos (φ ((x.1 : Fin L), (x.2 : Fin L)))) =
        ∑ q ∈ chargeConfigsInternal Λ 1, (∏ x, hardCoreWeightInternal z (q x)) *
          Real.cos (∑ j, φ j * (push q j : ℝ)) := by
    intro φ
    rw [← Finset.prod_coe_sort Λ]
    have := prod_sineGordonWeight_eq_sum 1 (fun _ : Λ => hardCoreWeightInternal z)
      (fun _ n => hardCoreWeight_neg z n) (fun x => φ (red x))
    simp only [sineGordonWeight_hardCore] at this
    rw [this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hpush]
  have hint : ∀ q : Λ → ℤ, Integrable (fun φ : Fin L × Fin L → ℝ =>
      (∏ x, hardCoreWeightInternal z (q x)) * Real.cos (∑ j, φ j * (push q j : ℝ))) μ := by
    intro q
    refine Integrable.const_mul ?_ _
    have hc : Continuous fun φ : Fin L × Fin L → ℝ => Real.cos (∑ j, φ j * (push q j : ℝ)) :=
      Real.continuous_cos.comp (continuous_finsetSum _ fun j _ =>
        (continuous_apply j).mul continuous_const)
    refine Integrable.of_bound hc.aestronglyMeasurable 1 (ae_of_all _ fun φ => ?_)
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hval : ∀ q : Λ → ℤ, ∫ φ, Real.cos (∑ j, φ j * (push q j : ℝ)) ∂μ =
      if ∑ x, q x = 0 then
        Real.exp (-(Multigraph.pairing (fun j => (push q j : ℝ))
          (-(squarePeriodic L).greenOp (squarePeriodic_connected L hL)
            (fun j => (push q j : ℝ)))) / (2 * β⁻¹)) else 0 := by
    intro q
    have := integral_cos_charge_gffLaw (squarePeriodic L) (squarePeriodic_connected L hL) β⁻¹
      (inv_pos.mpr hβ) 0 (push q) 0
    simp only [add_zero, Real.cos_zero, mul_one, hpushsum] at this
    exact this
  unfold periodicHardCorePartition
  simp only [hexp]
  rw [integral_finsetSum _ fun q _ => hint q]
  simp only [integral_const_mul, hval]
  have h0 : (0 : Λ → ℤ) ∈ chargeConfigsInternal Λ 1 := by
    simp [chargeConfigsInternal, Fintype.mem_piFinset]
  rw [← Finset.add_sum_erase _ _ h0]
  have hfirst : (∏ x : Λ, hardCoreWeightInternal z ((0 : Λ → ℤ) x)) *
      (if ∑ x : Λ, (0 : Λ → ℤ) x = 0 then Real.exp (-(Multigraph.pairing
        (fun j => (push 0 j : ℝ)) (-(squarePeriodic L).greenOp (squarePeriodic_connected L hL)
          (fun j => (push 0 j : ℝ)))) / (2 * β⁻¹)) else 0) = 1 := by
    have hp0 : (fun j => (push 0 j : ℝ)) = 0 := by
      funext j; simp [push]
    simp [hp0, hardCoreWeightInternal, Multigraph.pairing]
  rw [hfirst]
  refine lt_add_of_pos_of_le one_pos (Finset.sum_nonneg fun q hq => ?_)
  split_ifs with hsum
  · exact mul_nonneg (prod_hardCoreWeight_nonneg_of_neutral z q (Finset.mem_of_mem_erase hq) hsum)
      (Real.exp_pos _).le
  · simp

end FroehlichSpencer.BKT.Provider

end
