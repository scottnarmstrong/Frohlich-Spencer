/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ConditionLambdaGas
import Mathlib.Tactic

/-!
# Provider: the positivity gate of the general Coulomb gas

`Z_Λ ≥ λ(0)^{|Λ|} > 0`: the vacuum term of the convergent series of nonnegative weights.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation (pairC chargeEnergy_eq)
open FroehlichSpencer.BKT.Bridge.ConditionLambdaGas

/-- **The positivity gate**: `Z_Λ ≥ λ(0)^{|Λ|} > 0`. -/
theorem coulombGasPartition_pos (β : ℝ) (lam : ℤ → ℝ) (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0)
    (hS : IsCoulombGasSummable β lam) (Λ : Finset (ℤ × ℤ)) :
    0 < coulombGasPartition β lam hS Λ := by
  unfold coulombGasPartition
  refine lt_of_lt_of_le ?_ ((summable_coulombGasWeight hS Λ).le_tsum 0
    fun q _ => coulombGasWeight_nonneg hlam Λ q)
  rw [coulombGasWeight_zero]
  exact pow_pos hlam0 _

end FroehlichSpencer.BKT.Provider

end
