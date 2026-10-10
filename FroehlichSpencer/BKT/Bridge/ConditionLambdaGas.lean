/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Surface.ConditionLambda
public import FroehlichSpencer.BKT.Surface.CoulombGasPartition
public import FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation
public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaFree
import Mathlib.Tactic

/-!
# Bridge: the general Coulomb gas of FS81

* `coulombGasWeight_eq`: the weight (1.4)–(1.6), (1.14) is 's `gasWeightInternal` of the
  free potential.
* `conditionLambdaInternal_of`: Condition λ gives 's internal Condition λ (with `max α 0`).
* The tilted weights `λ(n) e^{n²}` and `gateThreshold` (used by the summability gate's provider and
  by the stage-L link `secondMoment_iteratedLimit`).
* Nonnegativity, the vacuum weight and summability of the weights; `abs_pairC_le` (`|⟨q, C f⟩|`).

The two gate proofs stay in their providers (`Provider/CoulombGasSummability.lean`,
`Provider/CoulombGasPartitionPos.lean`), so later code reaches the gates only through the
statement.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.ConditionLambdaGas

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation (pairC chargeEnergy_eq)

/--
The weight is the internal gas weight of the free potential on `Λ`.
-/
theorem coulombGasWeight_eq (β : ℝ) (lam : ℤ → ℝ) (Λ : Finset (ℤ × ℤ)) (q : Λ → ℤ) :
    coulombGasWeight β lam Λ q =
      gasWeightInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β (fun _ => lam) q := by
  unfold coulombGasWeight gasWeightInternal
  rw [chargeEnergy_eq]
  rfl

theorem const_nonneg {C α ε β : ℝ} {lam : ℤ → ℝ} (h : IsConditionLambda C α ε β lam) : 0 ≤ C := by
  have := (h.2 0).2
  simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero, mul_one] at this
  exact (abs_nonneg _).trans this

/--
Condition λ in the form gives the internal form with `α` replaced by `max α 0`.
-/
theorem conditionLambdaInternal_of {C α ε β : ℝ} {lam : ℤ → ℝ} (h : IsConditionLambda C α ε β lam) :
    ConditionLambdaInternal C (max α 0) ε β lam := by
  refine ⟨fun n => ((h.2 n).1).symm, fun n => ?_⟩
  refine (h.2 n).2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (const_nonneg h))
  have : 0 ≤ ((n : ℝ)) ^ 2 := sq_nonneg _
  nlinarith [le_max_left α 0]

/-- The weights tilted by `e^{n²}`. -/
def tilt (lam : ℤ → ℝ) (n : ℤ) : ℝ := lam n * Real.exp ((n : ℝ) ^ 2)

theorem gasWeight_tilt {V : Type*} [Fintype V] [DecidableEq V] (T : (V → ℝ) →ₗ[ℝ] V → ℝ)
    (κ : ℝ) (lam : ℤ → ℝ) (q : V → ℤ) :
    gasWeightInternal T κ (fun _ => tilt lam) q =
      gasWeightInternal T κ (fun _ => lam) q * Real.exp (∑ j, (q j : ℝ) ^ 2) := by
  unfold gasWeightInternal tilt
  split_ifs
  · rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    ring
  · simp

theorem abs_mul_exp_le (t x : ℝ) : t * |x| ≤ x ^ 2 + t ^ 2 / 4 := by
  nlinarith [sq_nonneg (|x| - t / 2), sq_abs x]

/-- The summability threshold. -/
def gateThreshold (α ε : ℝ) : ℝ := (max α 0 + 1) / (1 / 16 - ε)

theorem coulombGasWeight_nonneg {β : ℝ} {lam : ℤ → ℝ} (hlam : ∀ q, 0 ≤ lam q)
    (Λ : Finset (ℤ × ℤ)) (q : Λ → ℤ) : 0 ≤ coulombGasWeight β lam Λ q := by
  unfold coulombGasWeight
  split_ifs
  · exact mul_nonneg (Finset.prod_nonneg fun j _ => hlam _) (Real.exp_pos _).le
  · exact le_rfl

theorem coulombGasWeight_zero (β : ℝ) (lam : ℤ → ℝ) (Λ : Finset (ℤ × ℤ)) :
    coulombGasWeight β lam Λ 0 = lam 0 ^ Fintype.card Λ := by
  unfold coulombGasWeight
  simp

theorem summable_coulombGasWeight {β : ℝ} {lam : ℤ → ℝ} (hS : IsCoulombGasSummable β lam)
    (Λ : Finset (ℤ × ℤ)) : Summable (coulombGasWeight β lam Λ) := by
  simpa using hS Λ 0

section Pairing

variable (Λ : Finset (ℤ × ℤ))

/-- The charge pairing is bounded by a multiple of the total absolute charge. -/
theorem abs_pairC_le (q : Λ → ℤ) (f : Λ → ℝ) :
    |pairC Λ (fun j => (q j : ℝ)) f| ≤
      (∑ i : Λ, |∑ j : Λ, f j * coulombPotential ((i : ℤ × ℤ) - j)|) * ∑ i, |(q i : ℝ)| := by
  set S : Λ → ℝ := fun i => ∑ j, f j * coulombPotential ((i : ℤ × ℤ) - j) with hSdef
  have hpair : pairC Λ (fun j => (q j : ℝ)) f = ∑ i, (q i : ℝ) * S i := by
    unfold pairC
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hle : ∀ i, |S i| ≤ ∑ k, |S k| := fun i =>
    Finset.single_le_sum (f := fun k => |S k|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
  rw [hpair]
  calc |∑ i, (q i : ℝ) * S i| ≤ ∑ i, |(q i : ℝ)| * |S i| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp only [abs_mul]
    _ ≤ ∑ i, |(q i : ℝ)| * ∑ k, |S k| :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (abs_nonneg _)
    _ = (∑ k, |S k|) * ∑ i, |(q i : ℝ)| := by rw [← Finset.sum_mul]; ring

end Pairing

end FroehlichSpencer.BKT.Bridge.ConditionLambdaGas

end
