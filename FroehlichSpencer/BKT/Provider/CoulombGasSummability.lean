/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ConditionLambdaGas
import Mathlib.Tactic

/-!
# Provider: the summability gate of the general Coulomb gas

Above `gateThreshold α ε` the tilted weights `λ(n) e^{n²}` pass 's internal gate (coercivity
`E(q) ≥ ‖q‖²/16`), and `t|n| ≤ n² + t²/4` turns that into every exponential moment of the total
absolute charge.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation (pairC chargeEnergy_eq)
open FroehlichSpencer.BKT.Bridge.ConditionLambdaGas

/-- **The summability gate**: above `gateThreshold α ε` every Condition-λ gas is summable with
every exponential moment of the total absolute charge. -/
theorem isCoulombGasSummable_of_gate {C α ε β : ℝ} {lam : ℤ → ℝ}
    (h : IsConditionLambda C α ε β lam) (hβ : gateThreshold α ε < β) :
    IsCoulombGasSummable β lam := by
  intro Λ t
  have hd : 0 < 1 / 16 - ε := by linarith [h.1]
  have hβα : max α 0 + 1 < β * (1 / 16 - ε) := (div_lt_iff₀ hd).1 hβ
  have hβ0 : 0 ≤ β := by
    have := le_max_right α 0
    have := mul_pos_iff.1 (by linarith : (0 : ℝ) < β * (1 / 16 - ε))
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1.le
    · linarith
  have hC := const_nonneg h
  -- the tilted weights pass the internal gate
  have hgate : GateInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β
      (fun _ => tilt lam) := by
    refine ⟨hβ0, 1 / 16, α + ε * β + 1, C, hC, by nlinarith [le_max_left α 0], fun q hq => ?_,
      fun _ n => ?_⟩
    · have := free_chargeEnergy_ge (Subtype.val : Λ → ℤ × ℤ) Subtype.val_injective q hq
      linarith
    · unfold tilt
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |lam n| * Real.exp ((n : ℝ) ^ 2)
          ≤ C * Real.exp ((α + ε * β) * (n : ℝ) ^ 2) * Real.exp ((n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right (h.2 n).2 (Real.exp_pos _).le
        _ = C * Real.exp ((α + ε * β + 1) * (n : ℝ) ^ 2) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hsum := hgate.summable_mul (fun _ => 1) 1 (fun q => by
    simp only [abs_one, one_mul]
    have : 0 ≤ ∑ j, ((q j : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith)
  simp only [mul_one] at hsum
  refine Summable.of_norm_bounded (hsum.abs.mul_left (Real.exp (Fintype.card Λ * (t ^ 2 / 4)))) ?_
  intro q
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), coulombGasWeight_eq,
    gasWeight_tilt, abs_mul, abs_of_pos (Real.exp_pos (∑ j, ((q j : ℤ) : ℝ) ^ 2))]
  have hexp : Real.exp (t * ∑ j, |(q j : ℝ)|) ≤
      Real.exp (Fintype.card Λ * (t ^ 2 / 4)) * Real.exp (∑ j, ((q j : ℤ) : ℝ) ^ 2) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    rw [Finset.mul_sum]
    have : ∀ j, t * |(q j : ℝ)| ≤ ((q j : ℤ) : ℝ) ^ 2 + t ^ 2 / 4 := fun j => abs_mul_exp_le t _
    calc ∑ j, t * |(q j : ℝ)| ≤ ∑ j, (((q j : ℤ) : ℝ) ^ 2 + t ^ 2 / 4) :=
          Finset.sum_le_sum fun j _ => this j
      _ = _ := by rw [Finset.sum_add_distrib]; simp [Finset.sum_const, nsmul_eq_mul]; ring
  calc |gasWeightInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β (fun _ => lam) q| *
        Real.exp (t * ∑ j, |(q j : ℝ)|)
      ≤ |gasWeightInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β (fun _ => lam) q| *
          (Real.exp (Fintype.card Λ * (t ^ 2 / 4)) * Real.exp (∑ j, ((q j : ℤ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
    _ = _ := by ring

/--
The summability gate in the form.
-/
theorem conditionLambda_isCoulombGasSummable :
    ∀ α ε : ℝ, ∃ β₀ : ℝ, ∀ C β : ℝ, β₀ < β → ∀ lam : ℤ → ℝ, IsConditionLambda C α ε β lam →
      IsCoulombGasSummable β lam :=
  fun α ε => ⟨gateThreshold α ε, fun _ _ hβ _ h => isCoulombGasSummable_of_gate h hβ⟩

end FroehlichSpencer.BKT.Provider

end
