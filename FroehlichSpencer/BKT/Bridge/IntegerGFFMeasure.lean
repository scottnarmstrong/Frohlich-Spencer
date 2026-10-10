/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.IntegerField
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # The pinned integer field's counting-measure normalization -/

@[expose] public section

namespace FroehlichSpencer.BKT

open MeasureTheory
open Multigraph

universe u v

variable {V : Type u} {E : Type v}

/-- The mixed product of a root Dirac mass and counting measures has one unit atom at each
integer field pinned to zero at the root. -/
theorem integerGFFBase_singleton [Fintype V] [DecidableEq V] (root : V) (m : V → ℤ) :
    (Measure.pi (fun j : V =>
      if j = root then Measure.dirac (0 : ℤ) else Measure.count)) {m} =
        if m root = 0 then 1 else 0 := by
  classical
  let ν : V → Measure ℤ := fun j =>
    if j = root then Measure.dirac 0 else Measure.count
  have hν (j : V) : SigmaFinite (ν j) := by
    dsimp [ν]
    split_ifs <;> infer_instance
  change (Measure.pi ν) {m} = _
  rw [@Measure.pi_singleton V (fun _ => ℤ) _ _ ν hν m]
  rw [Finset.prod_eq_single root]
  · by_cases hm : m root = 0 <;> simp [ν, hm]
  · intro j hj hjr
    simp [ν, hjr]
  · simp [ν]

/--
The total mass of the unnormalized  IGFF density is exactly the discrete KP partition
sum over fields pinned at the root, with each graph edge counted once.
-/
theorem integerGFFDensityMeasure_univ [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (hG : G.Connected) (β : ℝ) (hβ : 0 < β) (root : V) :
    ((Measure.pi (fun j : V =>
      if j = root then Measure.dirac (0 : ℤ) else Measure.count)).withDensity
        (fun m => ENNReal.ofReal (Real.exp (-(β / 2) *
          ∑ e, ((m (G.src e) : ℝ) - (m (G.tgt e) : ℝ)) ^ 2)))) Set.univ =
      ENNReal.ofReal (igffPartitionFunction G β root) := by
  classical
  rw [withDensity_apply _ MeasurableSet.univ]
  rw [lintegral_countable']
  simp only [Measure.restrict_univ]
  have hSingleton (m : V → ℤ) :
      (Measure.pi (fun j : V =>
        if j = root then Measure.dirac (0 : ℤ) else Measure.count)) {m} =
          if m root = 0 then 1 else 0 := integerGFFBase_singleton root m
  have hsub :
      (∑' m : ↑({m : V → ℤ | m root = 0}), ENNReal.ofReal (Real.exp (-(β / 2) *
        ∑ e, (((m : V → ℤ) (G.src e) : ℝ) - ((m : V → ℤ) (G.tgt e) : ℝ)) ^ 2))) =
      ∑' m : V → ℤ, if m root = 0 then ENNReal.ofReal (Real.exp (-(β / 2) *
        ∑ e, ((m (G.src e) : ℝ) - (m (G.tgt e) : ℝ)) ^ 2)) else 0 := by
    simpa [Set.indicator] using
      (tsum_subtype {m : V → ℤ | m root = 0} (fun m => ENNReal.ofReal (Real.exp
        (-(β / 2) * ∑ e, ((m (G.src e) : ℝ) - (m (G.tgt e) : ℝ)) ^ 2))))
  calc
    (∑' m : V → ℤ,
        ENNReal.ofReal (Real.exp (-(β / 2) *
          ∑ e, ((m (G.src e) : ℝ) - (m (G.tgt e) : ℝ)) ^ 2)) *
          (Measure.pi (fun j : V =>
            if j = root then Measure.dirac (0 : ℤ) else Measure.count)) {m}) =
        ∑' m : V → ℤ, if m root = 0 then
          ENNReal.ofReal (Real.exp (-(β / 2) *
            ∑ e, ((m (G.src e) : ℝ) - (m (G.tgt e) : ℝ)) ^ 2)) else 0 := by
      apply tsum_congr
      intro m
      rw [hSingleton m]
      by_cases hm : m root = 0 <;> simp [hm]
    _ = ∑' m : pinnedIntegerField V root, ENNReal.ofReal (Real.exp (-(β / 2) *
        ∑ e, ((m.1 (G.src e) : ℝ) - (m.1 (G.tgt e) : ℝ)) ^ 2)) := hsub.symm
    _ = ∑' m : pinnedIntegerField V root, ENNReal.ofReal (igffWeight G β m) := by
      apply tsum_congr
      intro m
      exact congrArg ENNReal.ofReal (igffWeight_eq_kp G β m).symm
    _ = ENNReal.ofReal (igffPartitionFunction G β root) := by
      rw [igffPartitionFunction]
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (f := fun m : pinnedIntegerField V root => igffWeight G β m)
        (fun m => (Real.exp_pos _).le)
        (summable_igffWeight G hG β hβ root)]

end FroehlichSpencer.BKT

end
