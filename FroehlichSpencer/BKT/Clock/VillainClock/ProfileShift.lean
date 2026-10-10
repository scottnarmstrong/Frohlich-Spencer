/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.ShiftLowerBound
import Mathlib.Tactic

/-!
# Gaussian lower bound for arbitrary Villain-clock edge profiles

For any edge shift field on a finite Villain-clock graph, the twisted partition function is at
least the unshifted one times the Gaussian cost of the shift.

The proof uses reflection of the
clock labels and the symmetric shift inequality for the periodized Gaussian.

This is a local
ingredient for a vortex-profile argument; representing the fractional disorder observable by a
logarithmic-energy profile remains a separate adapter.
-/

@[expose] public section

noncomputable section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Clock.VillainClock

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- The configuration weight after adding a real profile to every oriented edge. -/
def villainProfileConfigurationWeight {V E : Type*} [Fintype E]
    (G : Multigraph V E) (β : ℝ) (N : ℕ) (δ : E → ℝ) (s : V → Fin N) : ℝ :=
  ∏ e, villainWeight β (G.grad (angleField N s) e + δ e)

/-- The finite partition function with an arbitrary edge shift profile. -/
def villainProfilePartitionFunction {V E : Type*} [Fintype E] {N : ℕ}
    [Fintype (V → Fin N)] (G : Multigraph V E) (β : ℝ) (δ : E → ℝ) : ℝ :=
  ∑ s, villainProfileConfigurationWeight G β N δ s

theorem villainProfileConfigurationWeight_reverse {V E : Type*} [Fintype E]
    {N : ℕ} (hN : 0 < N) (G : Multigraph V E) (β : ℝ)
    (δ : E → ℝ) (s : V → Fin N) :
    villainProfileConfigurationWeight G β N δ (reverseClockConfig hN s) =
      villainProfileConfigurationWeight G β N (-δ) s := by
  unfold villainProfileConfigurationWeight
  apply Finset.prod_congr rfl
  intro e he
  rw [grad_reverse hN G s e]
  rw [show -(G.grad (angleField N s) e) + δ e =
    -(G.grad (angleField N s) e + (-δ e)) by ring]
  exact VillainWeight.villainWeight_neg β _

theorem villainProfilePartitionFunction_neg_eq {V E : Type*} [Fintype E]
    {N : ℕ} [Fintype (V → Fin N)] (hN : 0 < N) (G : Multigraph V E) (β : ℝ)
    (δ : E → ℝ) :
    villainProfilePartitionFunction (N := N) G β δ =
      villainProfilePartitionFunction (N := N) G β (-δ) := by
  unfold villainProfilePartitionFunction
  rw [← Equiv.sum_comp (reverseClockConfigEquiv N hN)]
  apply Finset.sum_congr rfl
  intro s hs
  exact villainProfileConfigurationWeight_reverse hN G β δ s

theorem villainProfileConfigurationWeight_pair_ge {V E : Type*} [Fintype E]
    {N : ℕ} {β : ℝ} (hβ : 0 < β) (G : Multigraph V E) (δ : E → ℝ)
    (s : V → Fin N) :
    Real.exp (-β * ∑ e, δ e ^ 2) * configurationWeight G β N s ^ 2 ≤
      villainProfileConfigurationWeight G β N δ s *
        villainProfileConfigurationWeight G β N (-δ) s := by
  classical
  have hpoint (e : E) :
      Real.exp (-β * δ e ^ 2) * villainWeight β (G.grad (angleField N s) e) ^ 2 ≤
        villainWeight β (G.grad (angleField N s) e + δ e) *
          villainWeight β (G.grad (angleField N s) e - δ e) := by
    simpa [sub_eq_add_neg] using
      villainWeight_shift_product β (G.grad (angleField N s) e) (δ e) hβ
  have hprod := Finset.prod_le_prod₀
    (s := Finset.univ) (fun e _ => by positivity) (fun e _ => hpoint e)
  have hE : (∏ e : E, Real.exp (-β * δ e ^ 2)) =
      Real.exp (-β * ∑ e, δ e ^ 2) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
  have hW : (∏ e : E, villainWeight β (G.grad (angleField N s) e) ^ 2) =
      configurationWeight G β N s ^ 2 := by
    simp [configurationWeight, Multigraph.grad, ← Finset.prod_pow]
  have hleft :
      (∏ e : E, Real.exp (-β * δ e ^ 2) *
        villainWeight β (G.grad (angleField N s) e) ^ 2) =
        Real.exp (-β * ∑ e, δ e ^ 2) * configurationWeight G β N s ^ 2 := by
    rw [Finset.prod_mul_distrib, hE, hW]
  rw [hleft] at hprod
  simpa [villainProfileConfigurationWeight, configurationWeight, sub_eq_add_neg,
    Finset.prod_mul_distrib, Multigraph.grad] using hprod

/-- An arbitrary real edge-shift profile costs its squared `ℓ²` norm in the finite
Villain-clock partition ratio. No seam-shape restriction is imposed on `δ`. -/
theorem villainProfilePartitionFunction_lower {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] {N : ℕ} [Fintype (V → Fin N)] (hN : 0 < N) {β : ℝ}
    (hβ : 0 < β) (G : Multigraph V E) (δ : E → ℝ) :
    Real.exp (-β / 2 * ∑ e, δ e ^ 2) *
      (∑ s : V → Fin N, configurationWeight G β N s) ≤
        villainProfilePartitionFunction (N := N) G β δ := by
  classical
  let Z := ∑ s : V → Fin N, configurationWeight G β N s
  let T := villainProfilePartitionFunction (N := N) G β δ
  let Tm := villainProfilePartitionFunction (N := N) G β (-δ)
  have hZ : 0 < Z := by
    dsimp [Z]
    exact Finset.sum_pos (fun s _ => configurationWeight_pos G hβ N s)
      ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩
  have hT : 0 < T := by
    dsimp [T, villainProfilePartitionFunction]
    exact Finset.sum_pos (fun s _ => Finset.prod_pos fun e _ =>
      VillainWeight.villainWeight_pos hβ _)
      ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩
  have hTm : 0 < Tm := by
    dsimp [Tm, villainProfilePartitionFunction]
    exact Finset.sum_pos (fun s _ => Finset.prod_pos fun e _ =>
      VillainWeight.villainWeight_pos hβ _)
      ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩
  have hpoint (s : V → Fin N) :
      2 * Real.sqrt (Real.exp (-β * ∑ e, δ e ^ 2)) * configurationWeight G β N s ≤
        villainProfileConfigurationWeight G β N δ s +
          villainProfileConfigurationWeight G β N (-δ) s := by
    have hp := villainProfileConfigurationWeight_pair_ge hβ G δ s
    have hp' : Real.exp (-β * ∑ e, δ e ^ 2) * configurationWeight G β N s ^ 2 ≤
        villainProfileConfigurationWeight G β N δ s *
          villainProfileConfigurationWeight G β N (-δ) s := hp
    have hA : 0 < villainProfileConfigurationWeight G β N δ s :=
      Finset.prod_pos fun e _ => VillainWeight.villainWeight_pos hβ _
    have hB : 0 < villainProfileConfigurationWeight G β N (-δ) s :=
      Finset.prod_pos fun e _ => VillainWeight.villainWeight_pos hβ _
    have hW : 0 < configurationWeight G β N s := configurationWeight_pos G hβ N s
    have hroot : Real.sqrt (Real.exp (-β * ∑ e, δ e ^ 2)) ^ 2 =
        Real.exp (-β * ∑ e, δ e ^ 2) := Real.sq_sqrt (Real.exp_nonneg _)
    have hsq :
        (2 * Real.sqrt (Real.exp (-β * ∑ e, δ e ^ 2)) *
          configurationWeight G β N s) ^ 2 ≤
        (villainProfileConfigurationWeight G β N δ s +
          villainProfileConfigurationWeight G β N (-δ) s) ^ 2 := by
      nlinarith [sq_nonneg (villainProfileConfigurationWeight G β N δ s -
        villainProfileConfigurationWeight G β N (-δ) s), hp', hroot]
    exact le_of_sq_le_sq hsq (add_nonneg hA.le hB.le)
  have hsum : 2 * Real.sqrt (Real.exp (-β * ∑ e, δ e ^ 2)) * Z ≤ T + Tm := by
    have := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hpoint s
    simpa [Z, T, Tm, villainProfilePartitionFunction, Finset.mul_sum,
      Finset.sum_add_distrib] using this
  have heq : T = Tm := by
    dsimp [T, Tm]
    exact villainProfilePartitionFunction_neg_eq hN G β δ
  have hratio : Real.sqrt (Real.exp (-β * ∑ e, δ e ^ 2)) * Z ≤ T := by
    nlinarith [hsum, heq]
  have hsqrt : Real.sqrt (Real.exp (-β * ∑ e, δ e ^ 2)) =
      Real.exp (-β / 2 * ∑ e, δ e ^ 2) := by
    have hroot := Real.sq_sqrt (Real.exp_nonneg (-β * ∑ e, δ e ^ 2))
    have hexp : Real.exp (-β / 2 * ∑ e, δ e ^ 2) ^ 2 =
        Real.exp (-β * ∑ e, δ e ^ 2) := by
      rw [show -β * ∑ e, δ e ^ 2 = 2 * (-β / 2 * ∑ e, δ e ^ 2) by ring,
        ← Real.exp_nat_mul]
      norm_num
    nlinarith [hroot, hexp, Real.sqrt_nonneg (Real.exp (-β * ∑ e, δ e ^ 2)),
      Real.exp_nonneg (-β / 2 * ∑ e, δ e ^ 2)]
  rw [hsqrt] at hratio
  exact hratio

/-- Logarithmic energy of the edge profile gives a power-shaped finite-volume lower bound. The
theorem is conditional on the profile-energy estimate and does not assert the Villain disorder
profile-transfer identity. -/
theorem villainProfilePartitionFunction_lower_of_log_energy {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq V] {N : ℕ} [Fintype (V → Fin N)] (hN : 0 < N) {β : ℝ}
    (hβ : 0 < β) (G : Multigraph V E) (δ : E → ℝ) (r ξ C₀ : ℝ)
    (henergy : ∑ e, δ e ^ 2 ≤ ξ ^ 2 * C₀ * (1 + Real.log (1 + r))) :
    Real.exp (-β / 2 * (ξ ^ 2 * C₀ * (1 + Real.log (1 + r)))) *
      (∑ s : V → Fin N, configurationWeight G β N s) ≤
        villainProfilePartitionFunction (N := N) G β δ := by
  have hbase := villainProfilePartitionFunction_lower hN hβ G δ
  have hZ : 0 ≤ ∑ s : V → Fin N, configurationWeight G β N s := by
    apply Finset.sum_nonneg
    intro s hs
    exact (configurationWeight_pos G hβ N s).le
  have hexp : Real.exp (-β / 2 * (ξ ^ 2 * C₀ * (1 + Real.log (1 + r)))) ≤
      Real.exp (-β / 2 * ∑ e, δ e ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hcoef : -β / 2 ≤ 0 := by linarith
    exact mul_le_mul_of_nonpos_left henergy hcoef
  calc
    _ ≤ Real.exp (-β / 2 * ∑ e, δ e ^ 2) *
        (∑ s : V → Fin N, configurationWeight G β N s) :=
      mul_le_mul_of_nonneg_right hexp hZ
    _ ≤ villainProfilePartitionFunction (N := N) G β δ := hbase

end FroehlichSpencer.BKT.Clock.VillainClock

end
