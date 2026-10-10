/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.DisorderCarrier
public import FroehlichSpencer.BKT.Clock.VillainClock.ShiftBounds
import Mathlib.Tactic

/-!
# Symmetric finite-volume lower bound for Villain-clock disorder

The symmetric real-shift inequality for the periodized Gaussian gives a direct lower bound for
every fractional twist `ξ`, without requiring `N ξ` to be integral.

Reflection of the clock labels
identifies the two opposite seam twists.

This yields an exponential-in-seam-length estimate and
its transfer to every selected free-square limit point; it is weaker than FS81 (7.5), whose
logarithmic vortex-profile estimate remains to be proved.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Clock.VillainClock
open FroehlichSpencer.BKT.Rotator

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

def reverseClock {N : ℕ} (_hN : 0 < N) (k : Fin N) : Fin N :=
  ⟨N - 1 - k.val, by have hk := k.isLt; omega⟩

theorem reverseClock_val {N : ℕ} (_hN : 0 < N) (k : Fin N) :
    (reverseClock _hN k).val = N - 1 - k.val := rfl

theorem reverseClock_involutive {N : ℕ} (hN : 0 < N) (k : Fin N) :
    reverseClock hN (reverseClock hN k) = k := by
  apply Fin.ext
  simp only [reverseClock_val hN]
  have hk := k.isLt
  omega

def reverseClockEquiv (N : ℕ) (hN : 0 < N) : Fin N ≃ Fin N where
  toFun := reverseClock hN
  invFun := reverseClock hN
  left_inv := reverseClock_involutive hN
  right_inv := reverseClock_involutive hN

def reverseClockConfig {V : Type*} {N : ℕ} (hN : 0 < N) (s : V → Fin N) : V → Fin N :=
  fun v => reverseClock hN (s v)

def reverseClockConfigEquiv {V : Type*} (N : ℕ) (hN : 0 < N) : (V → Fin N) ≃ (V → Fin N) where
  toFun := reverseClockConfig hN
  invFun := reverseClockConfig hN
  left_inv := by intro s; funext v; exact reverseClock_involutive hN (s v)
  right_inv := by intro s; funext v; exact reverseClock_involutive hN (s v)

theorem clockAngle_reverse {N : ℕ} (hN : 0 < N) (k : Fin N) :
    clockAngle N (reverseClock hN k) = 2 * Real.pi - 2 * Real.pi / N - clockAngle N k := by
  unfold clockAngle
  rw [reverseClock_val hN]
  have hN1 : 1 ≤ N := hN
  have hkNat : k.val ≤ N - 1 := by omega
  have hcast : ((N - 1 - k.val : ℕ) : ℝ) = (N : ℝ) - 1 - (k.val : ℝ) := by
    rw [Nat.cast_sub hkNat, Nat.cast_sub hN1]
    ring
  rw [hcast]
  field_simp [ne_of_gt (show (0 : ℝ) < N by exact_mod_cast hN)]

theorem angleField_reverse {V : Type*} {N : ℕ} (hN : 0 < N) (s : V → Fin N) (v : V) :
    angleField N (reverseClockConfig hN s) v =
      2 * Real.pi - 2 * Real.pi / N - angleField N s v := by
  exact clockAngle_reverse hN (s v)

theorem grad_reverse {V E : Type*} [Fintype E] {N : ℕ} (hN : 0 < N)
    (G : Multigraph V E) (s : V → Fin N) (e : E) :
    G.grad (angleField N (reverseClockConfig hN s)) e =
      -(G.grad (angleField N s) e) := by
  simp only [Multigraph.grad, angleField_reverse]
  ring

theorem configurationWeight_reverse {V E : Type*} [Fintype E] {N : ℕ} (hN : 0 < N)
    (G : Multigraph V E) (β : ℝ) (s : V → Fin N) :
    configurationWeight G β N (reverseClockConfig hN s) = configurationWeight G β N s := by
  unfold configurationWeight
  change ∏ e, villainWeight β (G.grad (angleField N (reverseClockConfig hN s)) e) = _
  apply Finset.prod_congr rfl
  intro e he
  rw [grad_reverse hN]
  exact VillainWeight.villainWeight_neg β _

theorem twistedWeight_reverse {V E : Type*} [Fintype E] [DecidableEq E] {N : ℕ}
    (hN : 0 < N) (G : Multigraph V E) (M : Finset E) (β ξ : ℝ) (s : V → Fin N) :
    twistedConfigurationWeight G M β ξ N (reverseClockConfig hN s) =
      twistedConfigurationWeight G M β (-ξ) N s := by
  unfold twistedConfigurationWeight
  change ∏ e, villainWeight β (G.grad (angleField N (reverseClockConfig hN s)) e +
      if e ∈ M then 2 * Real.pi * ξ else 0) =
    ∏ e, villainWeight β (G.grad (angleField N s) e +
      if e ∈ M then 2 * Real.pi * -ξ else 0)
  apply Finset.prod_congr rfl
  intro e he
  rw [grad_reverse hN]
  by_cases hm : e ∈ M
  · simp only [ite_eq_left hm]
    have harg : -G.grad (angleField N s) e + 2 * Real.pi * ξ =
        -(G.grad (angleField N s) e + 2 * Real.pi * (-ξ)) := by ring
    rw [harg, VillainWeight.villainWeight_neg]
  · simp only [ite_eq_right hm, add_zero]
    rw [VillainWeight.villainWeight_neg]

theorem twistedPartitionFunction_neg_eq {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] {N : ℕ} (hN : 0 < N)
    (G : Multigraph V E) (M : Finset E) (β ξ : ℝ) :
    twistedPartitionFunction G M β ξ N = twistedPartitionFunction G M β (-ξ) N := by
  unfold twistedPartitionFunction
  rw [← Equiv.sum_comp (reverseClockConfigEquiv N hN)]
  apply Finset.sum_congr rfl
  intro s hs
  exact twistedWeight_reverse hN G M β ξ s

theorem twistedWeight_pair_ge {V E : Type*} [Fintype E] [DecidableEq E]
    {N : ℕ} {β ξ : ℝ} (hβ : 0 < β)
    (G : Multigraph V E) (M : Finset E) (s : V → Fin N) :
    (Real.exp (-β * (2 * Real.pi * ξ) ^ 2) ^ M.card) *
        configurationWeight G β N s ^ 2 ≤
      twistedConfigurationWeight G M β ξ N s *
        twistedConfigurationWeight G M β (-ξ) N s := by
  classical
  let q : ℝ := Real.exp (-β * (2 * Real.pi * ξ) ^ 2)
  have hq : 0 < q := Real.exp_pos _
  have hpoint (e : E) :
      (if e ∈ M then q else 1) *
          villainWeight β (G.grad (angleField N s) e) ^ 2 ≤
        villainWeight β (G.grad (angleField N s) e +
          if e ∈ M then 2 * Real.pi * ξ else 0) *
        villainWeight β (G.grad (angleField N s) e +
          if e ∈ M then 2 * Real.pi * (-ξ) else 0) := by
    by_cases hm : e ∈ M
    · simp only [ite_eq_left hm, q]
      have h := villainWeight_shift_product β (G.grad (angleField N s) e)
        (2 * Real.pi * ξ) hβ
      simpa [sub_eq_add_neg] using h
    · simp only [ite_eq_right hm, one_mul, add_zero]
      exact le_of_eq (by ring)
  have hprod := Finset.prod_le_prod₀
    (s := Finset.univ) (fun e _ => by positivity) (fun e _ => hpoint e)
  have hleft :
      (∏ e : E, (if e ∈ M then q else 1) *
        villainWeight β (G.grad (angleField N s) e) ^ 2) =
        q ^ M.card * configurationWeight G β N s ^ 2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_const,
      configurationWeight, ← Finset.prod_pow]
    simp [Multigraph.grad]
  rw [hleft] at hprod
  simpa [twistedConfigurationWeight, configurationWeight, q, Finset.prod_mul_distrib,
    Multigraph.grad] using hprod

theorem freeSquareDisorderExpectation_ge_villain_shift {r L : ℕ} (N : ℕ) (β ξ : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hL : 0 < L) (hr : r ≤ L) :
    Real.sqrt (Real.exp (-β * (2 * Real.pi * ξ) ^ 2) ^ r) ≤
      freeSquareDisorderExpectation N β ξ hβ hN hL hr := by
  classical
  let G := rotatorFreeGraph (2 * L)
  let M := freeSquareDisorderEdgeSet hL hr
  let C : ℝ := Real.exp (-β * (2 * Real.pi * ξ) ^ 2) ^ M.card
  have hC : 0 < C := by dsimp [C]; positivity
  let d : ℝ := Real.sqrt C
  have hd0 : 0 ≤ d := Real.sqrt_nonneg C
  have hd2 : d ^ 2 = C := by
    dsimp [d]
    exact Real.sq_sqrt hC.le
  have hZ : 0 < freeSquarePartitionFunction N L β :=
    freeSquarePartitionFunction_pos N L β hβ hN
  have hsumPoint (s : RotatorSpinSite (2 * L) → Fin N) :
      2 * d * freeSquareConfigurationWeight N L β s ≤
        twistedConfigurationWeight G M β ξ N s +
          twistedConfigurationWeight G M β (-ξ) N s := by
    have hpair := twistedWeight_pair_ge (N := N) (β := β) (ξ := ξ) hβ G M s
    have hpair' : C * freeSquareConfigurationWeight N L β s ^ 2 ≤
        twistedConfigurationWeight G M β ξ N s *
          twistedConfigurationWeight G M β (-ξ) N s := by
      simpa [C, G, M, freeSquareConfigurationWeight] using hpair
    have hA : 0 < twistedConfigurationWeight G M β ξ N s := by
      unfold twistedConfigurationWeight
      exact Finset.prod_pos fun e _ => VillainWeight.villainWeight_pos hβ _
    have hB : 0 < twistedConfigurationWeight G M β (-ξ) N s := by
      unfold twistedConfigurationWeight
      exact Finset.prod_pos fun e _ => VillainWeight.villainWeight_pos hβ _
    have hW : 0 < freeSquareConfigurationWeight N L β s := by
      exact configurationWeight_pos G hβ N s
    have hsq : (2 * d * freeSquareConfigurationWeight N L β s) ^ 2 ≤
        (twistedConfigurationWeight G M β ξ N s +
          twistedConfigurationWeight G M β (-ξ) N s) ^ 2 := by
      nlinarith [sq_nonneg (twistedConfigurationWeight G M β ξ N s -
        twistedConfigurationWeight G M β (-ξ) N s), hpair', hd2]
    exact le_of_sq_le_sq hsq (add_nonneg hA.le hB.le)
  have hsum :
      2 * d * freeSquarePartitionFunction N L β ≤
        twistedPartitionFunction G M β ξ N + twistedPartitionFunction G M β (-ξ) N := by
    have := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hsumPoint s
    simpa [freeSquarePartitionFunction, freeSquareConfigurationWeight, partitionFunction,
      twistedPartitionFunction, G, Finset.mul_sum, Finset.sum_add_distrib] using this
  have htwistEq : twistedPartitionFunction G M β ξ N =
      twistedPartitionFunction G M β (-ξ) N :=
    twistedPartitionFunction_neg_eq hN G M β ξ
  have hnum : d * freeSquarePartitionFunction N L β ≤
      twistedPartitionFunction G M β ξ N := by
    nlinarith [hsum, htwistEq]
  have hRatio' : d ≤
      twistedPartitionFunction G M β ξ N / freeSquarePartitionFunction N L β := by
    exact (le_div_iff₀ hZ).2 hnum
  rw [htwistEq] at hRatio'
  rw [freeSquareDisorderExpectation_eq_twistedPartition_ratio N β ξ hβ hN hL hr]
  have hcard : M.card = r := by
    dsimp [M, freeSquareDisorderEdgeSet]
    rw [Finset.card_image_of_injective _ (disorderSeamEdge_injective hL hr)]
    simp
  simpa [d, C, hcard] using hRatio'

theorem freeSquareDisorderIndexedLimit_ge_villain_shift {r : ℕ} (N : ℕ) (β ξ c : ℝ)
    (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
    (hc : IsFreeSquareDisorderIndexedLimit N r β ξ c hβ hN hr) :
    Real.sqrt (Real.exp (-β * (2 * Real.pi * ξ) ^ 2) ^ r) ≤ c := by
  apply freeSquareDisorderIndexedLimit_ge_of_uniformLower N r β ξ _ c hβ hN hr
  · intro t
    exact freeSquareDisorderExpectation_ge_villain_shift N β ξ hβ hN (by omega) (by omega)
  · exact hc

end FroehlichSpencer.BKT.Clock.VillainClock

end
