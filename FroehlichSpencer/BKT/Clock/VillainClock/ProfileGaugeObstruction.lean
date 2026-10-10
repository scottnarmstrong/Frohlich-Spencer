/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.ProfileShift
import Mathlib.Tactic

/-!
# A finite Villain-clock gauge obstruction

The Gaussian profile inequality applies to real edge shifts, but a finite clock sum is not
invariant under an arbitrary real vertex-gradient shift. The one-bond example below isolates why
the real vortex decomposition cannot simply be gauged away inside the finite clock partition sum.
This is an obstruction to that proof shortcut, not a counterexample to FS81 (7.5).
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.VillainWeight
open FroehlichSpencer.BKT.Clock.VillainClock

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

private def vFourierCoeff (β : ℝ) (q : ℤ) : ℝ :=
  Real.exp (-((q : ℝ) ^ 2) / (2 * β))

private theorem vFourierCoeff_summable {β : ℝ} (hβ : 0 < β) :
    Summable (vFourierCoeff β) := by
  change Summable (fun q : ℤ => Real.exp (-((q : ℝ) ^ 2) / (2 * β)))
  exact villainWeight_fourier_coeff_summable hβ

private theorem vFourierCoeff_cos_summable {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    Summable (fun q : ℤ => vFourierCoeff β q * Real.cos ((q : ℝ) * x)) := by
  apply Summable.of_norm_bounded (vFourierCoeff_summable hβ)
  intro q
  change |vFourierCoeff β q * Real.cos ((q : ℝ) * x)| ≤ vFourierCoeff β q
  dsimp [vFourierCoeff]
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-((q : ℝ) ^ 2) / (2 * β)) * |Real.cos ((q : ℝ) * x)| ≤
        Real.exp (-((q : ℝ) ^ 2) / (2 * β)) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_nonneg _)
    _ = vFourierCoeff β q := by simp [vFourierCoeff]

private theorem villainWeight_zero_gt_pi {β : ℝ} (hβ : 0 < β) :
    villainWeight β 0 > villainWeight β Real.pi := by
  have hs0 := vFourierCoeff_cos_summable hβ 0
  have hsπ := vFourierCoeff_cos_summable hβ Real.pi
  have hsumdiff :
      (∑' q : ℤ, vFourierCoeff β q * Real.cos ((q : ℝ) * 0)) -
        (∑' q : ℤ, vFourierCoeff β q * Real.cos ((q : ℝ) * Real.pi)) =
      ∑' q : ℤ, vFourierCoeff β q *
        (Real.cos ((q : ℝ) * 0) - Real.cos ((q : ℝ) * Real.pi)) := by
    rw [← hs0.tsum_sub hsπ]
    congr 1
    ext q
    ring
  have hnonneg (q : ℤ) : 0 ≤ vFourierCoeff β q *
      (Real.cos ((q : ℝ) * 0) - Real.cos ((q : ℝ) * Real.pi)) := by
    rw [show (q : ℝ) * 0 = 0 by ring, Real.cos_zero]
    exact mul_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr (Real.cos_le_one _))
  have hterm : 0 < vFourierCoeff β 1 *
      (Real.cos ((1 : ℝ) * 0) - Real.cos ((1 : ℝ) * Real.pi)) := by
    rw [show (1 : ℝ) * 0 = 0 by ring, Real.cos_zero,
      show (1 : ℝ) * Real.pi = Real.pi by ring, Real.cos_pi]
    norm_num [vFourierCoeff]
    positivity
  have hdiffSummable : Summable (fun q : ℤ => vFourierCoeff β q *
      (Real.cos ((q : ℝ) * 0) - Real.cos ((q : ℝ) * Real.pi))) := by
    have h := hs0.sub hsπ
    convert h using 1
    ext q
    ring
  have hsumpos : 0 < ∑' q : ℤ, vFourierCoeff β q *
      (Real.cos ((q : ℝ) * 0) - Real.cos ((q : ℝ) * Real.pi)) := by
    have hle := hdiffSummable.le_tsum (1 : ℤ) (fun q _ => hnonneg q)
    have hle' := hle
    norm_num at hterm
    have hle'' : 2 * vFourierCoeff β 1 ≤
        ∑' q : ℤ, vFourierCoeff β q *
          (Real.cos ((q : ℝ) * 0) - Real.cos ((q : ℝ) * Real.pi)) := by
      calc
        2 * vFourierCoeff β 1 = vFourierCoeff β 1 * (1 + 1) := by ring
        _ ≤ _ := by simpa [Real.cos_zero, Real.cos_pi] using hle'
    nlinarith [hterm, hle'']
  have hbase : 0 < (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) := by positivity
  have h0 := villainWeight_fourier_real hβ 0
  have hπ := villainWeight_fourier_real hβ Real.pi
  have hweightdiff : villainWeight β 0 - villainWeight β Real.pi =
      (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
        (∑' q : ℤ, vFourierCoeff β q *
          (Real.cos ((q : ℝ) * 0) - Real.cos ((q : ℝ) * Real.pi))) := by
    rw [h0, hπ]
    calc
      (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
          ∑' q : ℤ, vFourierCoeff β q * Real.cos ((q : ℝ) * 0) -
        (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
          ∑' q : ℤ, vFourierCoeff β q * Real.cos ((q : ℝ) * Real.pi) =
        (2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) *
          ((∑' q : ℤ, vFourierCoeff β q * Real.cos ((q : ℝ) * 0)) -
           (∑' q : ℤ, vFourierCoeff β q * Real.cos ((q : ℝ) * Real.pi))) := by ring
      _ = _ := by rw [hsumdiff]
  have hpos : 0 < villainWeight β 0 - villainWeight β Real.pi := by
    rw [hweightdiff]
    exact mul_pos hbase hsumpos
  linarith

def singleBondTestGraph : Multigraph (Fin 2) (Fin 1) where
  src := fun _ => 0
  tgt := fun _ => 1
  src_ne_tgt := by decide

def singleBondTestPotential : Fin 2 → ℝ := fun v => if v = 0 then Real.pi else 0

private theorem oneBondProfilePartition_zero (β : ℝ) :
    villainProfilePartitionFunction (N := 1) singleBondTestGraph β (fun _ => 0) =
      villainWeight β 0 := by
  classical
  let s₀ : Fin 2 → Fin 1 := fun _ => 0
  have hsum := @Fintype.sum_subsingleton ℝ (Fin 2 → Fin 1) inferInstance inferInstance
    Pi.instSubsingleton (fun s => villainProfileConfigurationWeight singleBondTestGraph β 1
      (fun _ => 0) s) s₀
  have hgrad : singleBondTestGraph.grad (angleField 1 s₀) 0 = 0 := by
    simp [Multigraph.grad, singleBondTestGraph, angleField, clockAngle, s₀]
  unfold villainProfilePartitionFunction
  rw [hsum]
  unfold villainProfileConfigurationWeight
  rw [@Fintype.prod_subsingleton ℝ (Fin 1) inferInstance inferInstance
    inferInstance _ 0]
  change villainWeight β (singleBondTestGraph.grad (angleField 1 s₀) 0 + 0) =
    villainWeight β 0
  rw [hgrad]
  simp

private theorem oneBondProfilePartition_gradient (β : ℝ) :
    villainProfilePartitionFunction (N := 1) singleBondTestGraph β
      (fun e => singleBondTestGraph.grad singleBondTestPotential e) =
      villainWeight β Real.pi := by
  classical
  let s₀ : Fin 2 → Fin 1 := fun _ => 0
  have hsum := @Fintype.sum_subsingleton ℝ (Fin 2 → Fin 1) inferInstance inferInstance
    Pi.instSubsingleton (fun s => villainProfileConfigurationWeight singleBondTestGraph β 1
      (fun e => singleBondTestGraph.grad singleBondTestPotential e) s) s₀
  have hgrad : ∀ e : Fin 1, singleBondTestGraph.grad singleBondTestPotential e = Real.pi := by
    intro e
    fin_cases e
    simp [Multigraph.grad, singleBondTestGraph, singleBondTestPotential]
  have hgradConfig : singleBondTestGraph.grad (angleField 1 s₀) 0 = 0 := by
    simp [Multigraph.grad, singleBondTestGraph, angleField, clockAngle, s₀]
  unfold villainProfilePartitionFunction
  rw [hsum]
  unfold villainProfileConfigurationWeight
  rw [@Fintype.prod_subsingleton ℝ (Fin 1) inferInstance inferInstance
    inferInstance _ 0]
  change villainWeight β
    (singleBondTestGraph.grad (angleField 1 s₀) 0 + singleBondTestGraph.grad singleBondTestPotential 0) =
      villainWeight β Real.pi
  rw [hgradConfig, hgrad 0]
  ring_nf

/-- The `N = 1` Villain-clock sum on one edge changes under a real vertex-gradient shift
of size `π`. Thus the real-gradient part of a vortex profile is not a gauge symmetry of the
finite clock carrier. -/
theorem villainProfilePartition_not_invariant_under_real_gradient {β : ℝ} (hβ : 0 < β) :
    villainProfilePartitionFunction (N := 1) singleBondTestGraph β (fun _ => 0) ≠
      villainProfilePartitionFunction (N := 1) singleBondTestGraph β
        (fun e => singleBondTestGraph.grad singleBondTestPotential e) := by
  rw [oneBondProfilePartition_zero, oneBondProfilePartition_gradient]
  exact (ne_of_gt (villainWeight_zero_gt_pi hβ))

end FroehlichSpencer.BKT.Clock.VillainClock

end
