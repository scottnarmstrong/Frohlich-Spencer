/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.ConditionLambdaActivity
public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaTheoremBObstruction
import Mathlib.Tactic

/-!
# Obstruction to a direct quotient-charge weight identification

The modular current sum has an exact quotient charge, but its summands are still edge-current
weights.

The current weight at `k=N`, normalized by its vacuum weight, has a different Gaussian
exponent from the corresponding Coulomb-gas weight.

This rules out that direct summand-preserving map.

It does not rule out an aggregate duality that
first sums or transforms over edge currents; no such identity is proved here.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

open FroehlichSpencer.BKT.Coulomb

/-- The lifted Gaussian edge-current weight for quotient current `k`, whose integer lift is `N k`.
-/
def quotientCurrentGaussianWeight (β : ℝ) (N : ℕ) (k : ℤ) : ℝ :=
  gaussianAliasTerm β ((N : ℤ) * k)


def aliasAdjacentDipoleGasWeight (β : ℝ) (N : ℕ) (k : ℤ) : ℝ :=
  gaussianAliasActivity β N k * gaussianAliasActivity β N (-k) *
    Real.exp (-gaussianAliasCoulombCoupling β N * (k : ℝ) ^ 2 *
      (adjacentDipoleQuadInternal / 2))


theorem aliasAdjacentDipoleGasWeight_zero_and_order {β : ℝ} (_hβ : 0 < β) {N : ℕ}
    (_hN : 0 < N) :
    aliasAdjacentDipoleGasWeight β N 0 = gaussianAliasActivity β N 0 ^ 2 ∧
      aliasAdjacentDipoleGasWeight β N N =
        gaussianAliasActivity β N 0 ^ 2 * Real.exp
          (-gaussianAliasCoulombCoupling β N * (N : ℝ) ^ 2 *
            (adjacentDipoleQuadInternal / 2)) := by
  have hper : gaussianAliasActivity β N (N : ℤ) = gaussianAliasActivity β N 0 := by
    simpa using gaussianAliasActivity_add_period β N 0 1
  have hneg : gaussianAliasActivity β N (-(N : ℤ)) = gaussianAliasActivity β N 0 := by
    rw [gaussianAliasActivity_even, hper]
  constructor
  · simp [aliasAdjacentDipoleGasWeight, pow_two]
  · simp [aliasAdjacentDipoleGasWeight, hper, hneg, pow_two]

/--
Thus the direct quotient-charge assignment is not a term-by-term finite-volume
duality, even on two adjacent sites.
-/
theorem no_common_scalar_for_direct_weight_identification {β : ℝ} (hβ : 0 < β) {N : ℕ}
    (hN : 0 < N) :
    ¬ ∃ c : ℝ, ∀ k : ℤ,
      quotientCurrentGaussianWeight β N k = c * aliasAdjacentDipoleGasWeight β N k := by
  rintro ⟨c, hc⟩
  have _hApos := gaussianAliasActivity_pos hβ hN 0
  have hAne : gaussianAliasActivity β N 0 ^ 2 ≠ 0 := by positivity
  have hzero := hc 0
  have horder := hc (N : ℤ)
  have hgas := (aliasAdjacentDipoleGasWeight_zero_and_order hβ hN).2
  have hperiodic := (aliasAdjacentDipoleGasWeight_zero_and_order hβ hN).1
  have hcurr0 : quotientCurrentGaussianWeight β N 0 = 1 := by
    simp [quotientCurrentGaussianWeight, gaussianAliasTerm]
  have hcurrN : quotientCurrentGaussianWeight β N (N : ℤ) =
      Real.exp (-((N : ℝ) ^ 4) / (2 * β)) := by
    unfold quotientCurrentGaussianWeight gaussianAliasTerm
    congr 1
    push_cast
    ring
  have hratio : quotientCurrentGaussianWeight β N (N : ℤ) =
      Real.exp (-gaussianAliasCoulombCoupling β N * (N : ℝ) ^ 2 *
        (adjacentDipoleQuadInternal / 2)) := by
    have hc0 : (1 : ℝ) = c * gaussianAliasActivity β N 0 ^ 2 := by
      simpa [hcurr0, hperiodic] using hzero
    have horder' : quotientCurrentGaussianWeight β N (N : ℤ) =
        c * (gaussianAliasActivity β N 0 ^ 2 * Real.exp
          (-gaussianAliasCoulombCoupling β N * (N : ℝ) ^ 2 *
            (adjacentDipoleQuadInternal / 2))) := by
      simpa [hgas] using horder
    have hcA : c * gaussianAliasActivity β N 0 ^ 2 = 1 := hc0.symm
    calc
      quotientCurrentGaussianWeight β N (N : ℤ) =
          c * (gaussianAliasActivity β N 0 ^ 2 * Real.exp
            (-gaussianAliasCoulombCoupling β N * (N : ℝ) ^ 2 *
              (adjacentDipoleQuadInternal / 2))) := horder'
      _ = Real.exp (-gaussianAliasCoulombCoupling β N * (N : ℝ) ^ 2 *
            (adjacentDipoleQuadInternal / 2)) := by rw [← mul_assoc, hcA, one_mul]
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hquad : adjacentDipoleQuadInternal ≤ 1 := adjacentDipoleQuad_le
  have hcoeff : (N : ℝ) ^ 4 * adjacentDipoleQuadInternal / (4 * β) ≤
      (N : ℝ) ^ 4 / (4 * β) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * β)
      (by positivity : (0 : ℝ) < 4 * β)]
    have hbase : (N : ℝ) ^ 4 * adjacentDipoleQuadInternal ≤ (N : ℝ) ^ 4 := by
      calc
        (N : ℝ) ^ 4 * adjacentDipoleQuadInternal ≤ (N : ℝ) ^ 4 * 1 :=
          mul_le_mul_of_nonneg_left hquad (show 0 ≤ (N : ℝ) ^ 4 by positivity)
        _ = (N : ℝ) ^ 4 := by ring
    have hmul := mul_le_mul_of_nonneg_right hbase (by positivity : 0 ≤ 4 * β)
    nlinarith
  have hstrict : (N : ℝ) ^ 4 / (4 * β) < (N : ℝ) ^ 4 / (2 * β) := by
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * β)
      (by positivity : (0 : ℝ) < 2 * β)]
    have hN4 : 0 < (N : ℝ) ^ 4 := by positivity
    nlinarith [hN4, hβ]
  have hcmp : (N : ℝ) ^ 4 * adjacentDipoleQuadInternal / (4 * β) <
      (N : ℝ) ^ 4 / (2 * β) := hcoeff.trans_lt hstrict
  have hcand : gaussianAliasCoulombCoupling β N * (N : ℝ) ^ 2 *
      (adjacentDipoleQuadInternal / 2) =
      (N : ℝ) ^ 4 * adjacentDipoleQuadInternal / (4 * β) := by
    unfold gaussianAliasCoulombCoupling
    have hform : (N : ℝ) ^ 2 / (2 * β) * (N : ℝ) ^ 2 *
        (adjacentDipoleQuadInternal / 2) =
          (N : ℝ) ^ 4 * adjacentDipoleQuadInternal / (4 * β) := by
      field_simp
      ring
    exact hform
  have hargs : -((N : ℝ) ^ 4) / (2 * β) <
      -gaussianAliasCoulombCoupling β N * (N : ℝ) ^ 2 *
        (adjacentDipoleQuadInternal / 2) := by
    calc
      -((N : ℝ) ^ 4) / (2 * β) < -((N : ℝ) ^ 4 * adjacentDipoleQuadInternal /
          (4 * β)) := by simpa [neg_div] using neg_lt_neg hcmp
      _ = -gaussianAliasCoulombCoupling β N * (N : ℝ) ^ 2 *
          (adjacentDipoleQuadInternal / 2) := by
            calc
              _ = -(gaussianAliasCoulombCoupling β N * (N : ℝ) ^ 2 *
                  (adjacentDipoleQuadInternal / 2)) := congrArg Neg.neg hcand.symm
              _ = _ := by ring
  have hexp := Real.exp_lt_exp.mpr hargs
  rw [hcurrN] at hratio
  exact (ne_of_lt hexp) hratio

end FroehlichSpencer.BKT.Clock.VillainClock

end
