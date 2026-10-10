/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ConditionLambdaGas
public import FroehlichSpencer.BKT.Surface.CoulombGasSummability
public import FroehlichSpencer.BKT.Surface.CoulombGasPartitionPos
public import FroehlichSpencer.BKT.Surface.ConditionLambdaSecondMoment
public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaLimit
public import FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree
import Mathlib.Tactic

/-!
# Bridge: the general second moment (1.16)–(1.17)

* `pairing_eq`, `sq_le_two_exp`, `summable_weight_mul_pairing_sq`,
  `secondMomentNumerator_summable`: the second-moment series converges on the whole carrier (`⟨q, C
  g⟩² ≤ 2 e^{M ∑|q_j|}`).
* `secondMoment_eq_full`: the second moment is 's `fullSecondMomentInternal` of the free
  potential (it consumes the positivity gate).
* `fullSecondMoment_normalize`, `conditionLambdaInternal_normalize`, `physical_normalize`: the
  normalization by `λ(0)`; `sum_region_eq_zero`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.ConditionLambdaSecondMoment

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation (pairC freeChargePairing_eq)
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMoment (finsupp_sum_eq_sum_region)
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree (quad_eq_freeQuad)
open FroehlichSpencer.BKT.Bridge.ConditionLambdaGas

section Moment

variable (Λ : Finset (ℤ × ℤ))

/--
`⟨q, C g⟩` in the form is the internal free pairing.
-/
theorem pairing_eq (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ) (q : Λ → ℤ) :
    (∑ i, (q i : ℝ) * g.sum fun y b => b * coulombPotential ((i : ℤ × ℤ) - y)) =
      freeChargePairingInternal (Subtype.val : Λ → ℤ × ℤ) (fun v => g v) q := by
  rw [freeChargePairing_eq]
  unfold pairC
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsupp_sum_eq_sum_region Λ g hgΛ (fun y => coulombPotential ((i : ℤ × ℤ) - y)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sq_le_two_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 2 ≤ 2 * Real.exp y := by
  have := Real.quadratic_le_exp_of_nonneg hy
  nlinarith

/-- The second-moment series converges: `w(q) ⟨q, C g⟩²` is dominated by `2 w(q) e^{M Σ|q_j|}`. -/
theorem summable_weight_mul_pairing_sq (β : ℝ) (lam : ℤ → ℝ) (hlam : ∀ q, 0 ≤ lam q)
    (hS : IsCoulombGasSummable β lam) (g : ℤ × ℤ →₀ ℝ) :
    Summable fun q : Λ → ℤ => coulombGasWeight β lam Λ q *
      freeChargePairingInternal (Subtype.val : Λ → ℤ × ℤ) (fun v => g v) q ^ 2 := by
  set P : (Λ → ℤ) → ℝ := fun q =>
    freeChargePairingInternal (Subtype.val : Λ → ℤ × ℤ) (fun v => g v) q with hP
  set M : ℝ := ∑ i : Λ, |∑ j : Λ, g j * coulombPotential ((i : ℤ × ℤ) - j)| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine Summable.of_nonneg_of_le
    (fun q => mul_nonneg (coulombGasWeight_nonneg hlam Λ q) (sq_nonneg _))
    (fun q => ?_) ((hS Λ M).mul_left 2)
  have hPle : |P q| ≤ M * ∑ i, |(q i : ℝ)| := by
    simp only [hP]
    rw [freeChargePairing_eq]
    exact abs_pairC_le Λ q (fun v => g v)
  have hs0 : 0 ≤ M * ∑ i, |(q i : ℝ)| :=
    mul_nonneg hM0 (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hsq : P q ^ 2 ≤ 2 * Real.exp (M * ∑ i, |(q i : ℝ)|) := by
    calc P q ^ 2 = |P q| ^ 2 := (sq_abs _).symm
      _ ≤ (M * ∑ i, |(q i : ℝ)|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hPle 2
      _ ≤ _ := sq_le_two_exp hs0
  calc coulombGasWeight β lam Λ q * P q ^ 2
      ≤ coulombGasWeight β lam Λ q * (2 * Real.exp (M * ∑ i, |(q i : ℝ)|)) :=
        mul_le_mul_of_nonneg_left hsq (coulombGasWeight_nonneg hlam Λ q)
    _ = 2 * (coulombGasWeight β lam Λ q * Real.exp (M * ∑ i, |(q i : ℝ)|)) := by ring

/-- **The (1.16)–(1.17) numerator converges** on the whole public carrier of
`conditionLambdaSecondMoment`. -/
theorem secondMomentNumerator_summable (β : ℝ) (lam : ℤ → ℝ) (hlam : ∀ q, 0 ≤ lam q)
    (hS : IsCoulombGasSummable β lam) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ) :
    Summable fun q : Λ → ℤ => coulombGasWeight β lam Λ q *
      (β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) -
        β ^ 2 * (∑ i, (q i : ℝ) * g.sum fun y b =>
          b * coulombPotential ((i : ℤ × ℤ) - y)) ^ 2) := by
  refine (((summable_coulombGasWeight hS Λ).mul_left
    (β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)))).sub
    ((summable_weight_mul_pairing_sq Λ β lam hlam hS g).mul_left (β ^ 2))).congr fun q => ?_
  rw [pairing_eq Λ g hgΛ q]
  ring

/--
**The bridge**: the second moment is 's full second moment.
-/
theorem secondMoment_eq_full (β : ℝ) (hβ : 0 < β) (lam : ℤ → ℝ) (hlam : ∀ q, 0 ≤ lam q)
    (hlam0 : 0 < lam 0) (hS : IsCoulombGasSummable β lam) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
    (hg : (g.sum fun _ a => a) = 0) :
    conditionLambdaSecondMoment β hβ lam hlam hlam0 hS Λ g hgΛ hg =
      fullSecondMomentInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β
        (fun _ => lam) (fun v => g v) := by
  have hZ := FroehlichSpencer.BKT.coulombGasPartition_pos β lam hlam hlam0 hS Λ
  have hw := summable_coulombGasWeight hS Λ
  have hw2 := summable_weight_mul_pairing_sq Λ β lam hlam hS g
  set P : (Λ → ℤ) → ℝ := fun q =>
    freeChargePairingInternal (Subtype.val : Λ → ℤ × ℤ) (fun v => g v) q with hP
  have hpair : ∀ q : Λ → ℤ,
      (∑ i, (q i : ℝ) * g.sum fun y b => b * coulombPotential ((i : ℤ × ℤ) - y)) = P q :=
    fun q => pairing_eq Λ g hgΛ q
  have hnum : (∑' q : Λ → ℤ, coulombGasWeight β lam Λ q *
      (β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) -
        β ^ 2 * (∑ i, (q i : ℝ) * g.sum fun y b => b * coulombPotential ((i : ℤ × ℤ) - y)) ^ 2)) =
      β * freeQuadInternal (Subtype.val : Λ → ℤ × ℤ) (fun v => g v) *
          ∑' q, coulombGasWeight β lam Λ q -
        β ^ 2 * ∑' q, coulombGasWeight β lam Λ q * P q ^ 2 := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hw.mul_left _).tsum_sub (hw2.mul_left _)]
    refine tsum_congr fun q => ?_
    rw [hpair q, quad_eq_freeQuad Λ g hgΛ]
    ring
  have hden : coulombGasPartition β lam hS Λ =
      fullGasPartitionInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β
        (fun _ => lam) := by
    unfold coulombGasPartition fullGasPartitionInternal
    exact tsum_congr fun q => coulombGasWeight_eq β lam Λ q
  have hsec : (∑' q, gasWeightInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β
      (fun _ => lam) q * (β * ∑ j, (q j : ℝ) *
        -(freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ) (fun v => g v) j)) ^ 2) =
      β ^ 2 * ∑' q, coulombGasWeight β lam Λ q * P q ^ 2 := by
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [← coulombGasWeight_eq]
    simp only [hP, freeChargePairingInternal]
    ring
  unfold conditionLambdaSecondMoment fullSecondMomentInternal fullGasExpectationInternal
  rw [hnum, ← hden, hsec]
  have hZ' := hZ.ne'
  unfold coulombGasPartition at hZ' ⊢
  rw [show (∑ j, (fun v : Λ => g v) j *
      -(freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ) (fun v => g v) j)) =
      freeQuadInternal (Subtype.val : Λ → ℤ × ℤ) (fun v => g v) from rfl]
  field_simp

end Moment

/-- Dividing the weights by `λ(0)` changes no full second moment. -/
theorem fullSecondMoment_normalize {V : Type*} [Fintype V] [DecidableEq V]
    (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : ℤ → ℝ) (h0 : lam 0 ≠ 0) (f : V → ℝ) :
    fullSecondMomentInternal T κ (fun _ n => (lam 0)⁻¹ * lam n) f =
      fullSecondMomentInternal T κ (fun _ => lam) f := by
  unfold fullSecondMomentInternal
  rw [fullGasExpectation_smul T κ (fun _ => lam) (fun _ => (lam 0)⁻¹)
    (Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero h0)]

/-- The normalized weights satisfy the internal Condition λ with constant `max C 0 / ν`. -/
theorem conditionLambdaInternal_normalize {C α ε β ν : ℝ} {lam : ℤ → ℝ}
    (h : IsConditionLambda C α ε β lam) (hν : 0 < ν) (hν0 : ν ≤ lam 0) :
    ConditionLambdaInternal (max C 0 / ν) α ε β (fun n => (lam 0)⁻¹ * lam n) := by
  have h0 : 0 < lam 0 := hν.trans_le hν0
  have hC := const_nonneg h
  refine ⟨fun n => by simp only [((h.2 n).1).symm], fun n => ?_⟩
  rw [abs_mul, abs_of_pos (inv_pos.2 h0), max_eq_left hC]
  have hE : 0 ≤ C * Real.exp ((α + ε * β) * (n : ℝ) ^ 2) := mul_nonneg hC (Real.exp_pos _).le
  calc (lam 0)⁻¹ * |lam n| ≤ (lam 0)⁻¹ * (C * Real.exp ((α + ε * β) * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (h.2 n).2 (inv_nonneg.2 h0.le)
    _ ≤ ν⁻¹ * (C * Real.exp ((α + ε * β) * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hν hν0) hE
    _ = C / ν * Real.exp ((α + ε * β) * (n : ℝ) ^ 2) := by ring

theorem physical_normalize {lam : ℤ → ℝ} (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0) :
    PhysicalWeightInternal (fun n => (lam 0)⁻¹ * lam n) :=
  ⟨inv_mul_cancel₀ hlam0.ne', fun n => mul_nonneg (inv_nonneg.2 hlam0.le) (hlam n)⟩

theorem sum_region_eq_zero (Λ : Finset (ℤ × ℤ)) (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ)
    (hg : (g.sum fun _ a => a) = 0) : ∑ v : Λ, g v = 0 := by
  have := finsupp_sum_eq_sum_region Λ g hgΛ (fun _ => 1)
  simp only [mul_one] at this
  rw [← this, hg]

end FroehlichSpencer.BKT.Bridge.ConditionLambdaSecondMoment

end
