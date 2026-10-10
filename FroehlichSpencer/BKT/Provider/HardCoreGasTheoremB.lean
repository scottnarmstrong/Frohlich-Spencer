/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation
public import FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree
public import FroehlichSpencer.BKT.Surface.HardCoreFracCorrelationLimit
public import FroehlichSpencer.BKT.Coulomb.ThermodynamicLimit
import Mathlib.Tactic

/-!
# Provider for `FroehlichSpencer.BKT.hardCoreGas_fracCorrelationLimit_upper_bound`

This module contains
`FroehlichSpencer.BKT.Provider.hardCoreGas_fracCorrelationLimit_upper_bound`, the proof of the
statement `FroehlichSpencer.BKT.hardCoreGas_fracCorrelationLimit_upper_bound` (file
`FroehlichSpencer/BKT/Surface/HardCoreGasTheoremB.lean`, FS81 Theorem B for the hard-core gas,
thermodynamic limits, in FS81's activity range (5.27)).

Existence: a joint subsequence of the boxes `[-k, k]²` ; every limit inherits
the finite bound.

The exponent is `β'(β) = c δ η² β` with `δ = 1/16 − max(ε, 0)`, `η = min(ξ, 1 − ξ)` and the
absolute `c` of the internal `coulombB_conditionLambda_free_fullRange_general`; the constant is
`A = 2 e^{β/(64δ)}`, uniform over the activity range `0 ≤ z ≤ K e^{εβ}` and the regions
(`Bridge.HardCoreFracCorrelation.finite_bound_activityRange`, through the bridge
`hardCoreFracCorrelation_eq_region` to the Condition-λ region correlation of the hard-core law).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter Topology
open FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.HardCoreFracCorrelation
open FroehlichSpencer.BKT.Bridge.HardCoreSecondMomentFree (subset_box)
open FroehlichSpencer.BKT.Generic.Marked (dipoleGap)

/-- **FS81 Theorem B, hard-core gas, infinite volume, in the activity range (5.27)**: as the
finite-volume root, for every activity `0 ≤ z ≤ K e^{εβ}` a thermodynamic limit exists and every
thermodynamic limit `G` satisfies `0 ≤ G(x) ≤ A |x|^{−β'(β)}` for `x ≠ 0`. -/
theorem hardCoreGas_fracCorrelationLimit_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∀ ε : ℝ, ε < 1 / 16 →
      ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧ ∀ K : ℝ,
        ∃ β₀ : ℝ, ∀ β : ℝ, β₀ < β → ∃ A : ℝ,
        ∀ (z : ℝ) (hz : 0 ≤ z), z ≤ K * Real.exp (ε * β) →
          (∃ G : ℤ × ℤ → ℝ, IsHardCoreFracCorrelationLimit β z hz ξ G) ∧
          ∀ G : ℤ × ℤ → ℝ, IsHardCoreFracCorrelationLimit β z hz ξ G →
            ∀ x : ℤ × ℤ, x ≠ 0 →
              0 ≤ G x ∧ G x ≤ A * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-β' β) := by
  classical
  intro ξ hξ0 hξ1 ε hε
  obtain ⟨c, hc, hK⟩ := finite_bound_activityRange hξ0 hξ1 hε
  refine ⟨fun β => c * (1 / 16 - max ε 0) * dipoleGap ξ ^ 2 * β,
    tendsto_exponent_activityRange hc hξ0 hξ1 hε, fun K => ?_⟩
  obtain ⟨κ₀, -, hB⟩ := hK K
  refine ⟨κ₀, fun β hβ =>
      ⟨2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * β), fun z hz hzK => ⟨?_, ?_⟩⟩⟩
  · -- existence: a joint subsequence of the boxes `[-k, k]²`
    set A := 2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * β) with hA
    set p := c * (1 / 16 - max ε 0) * dipoleGap ξ ^ 2 * β with hp
    set bound : ℤ × ℤ → ℝ := fun x =>
      if x = 0 then 1 else A * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-p)
    set u : ℕ → ℤ × ℤ → ℝ := fun k x =>
      if h : x ∈ boxInternal k then
        hardCoreFracCorrelation β z hz ξ (boxInternal k) ⟨0, zero_mem_box k⟩ ⟨x, h⟩
      else 0
    have hu : ∀ k x, |u k x| ≤ bound x := by
      intro k x
      simp only [u, bound]
      split_ifs with h hx
      · subst hx
        obtain ⟨h1, h2⟩ := hardCoreFracCorrelation_self_mem β z hz ξ
          (boxInternal k) ⟨0, zero_mem_box k⟩
        rw [abs_le]; constructor <;> linarith
      · obtain ⟨h1, h2⟩ := hB β hβ z hz hzK (boxInternal k) (zero_mem_box k) x h hx
        rw [abs_of_nonneg h1]; exact h2
      · subst_vars; simp
      · simp only [abs_zero]
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    obtain ⟨φ, hφ, G, hG⟩ := exists_subseq_tendsto_pointwise u bound hu
    have hbox : Tendsto (fun k => boxInternal (φ k)) atTop atTop :=
      tendsto_atTop_atTop.2 fun S => ⟨S.sup fun x => max x.1.natAbs x.2.natAbs,
        fun k hk => (subset_box S).trans (box_mono (hk.trans (hφ.id_le k)))⟩
    refine ⟨G, fun k => boxInternal (φ k), hbox, fun x => ?_⟩
    have hval := tendsto_val_regions hbox x
    refine ((hG x).comp hval).congr' (Eventually.of_forall fun k => ?_)
    simp only [Function.comp_apply, u, dite_eq_left k.2.2]
  · -- every thermodynamic limit
    intro G ⟨Λs, hΛs, hconv⟩ x hx0
    have := neBot_regions hΛs x
    have hk : ∀ k : {k : ℕ // (0 : ℤ × ℤ) ∈ Λs k ∧ x ∈ Λs k},
        0 ≤ hardCoreFracCorrelation β z hz ξ (Λs k) ⟨0, k.2.1⟩ ⟨x, k.2.2⟩ ∧
          hardCoreFracCorrelation β z hz ξ (Λs k) ⟨0, k.2.1⟩ ⟨x, k.2.2⟩ ≤
            2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * β) *
              Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^
                (-(c * (1 / 16 - max ε 0) * dipoleGap ξ ^ 2 * β)) :=
      fun k => hB β hβ z hz hzK (Λs k) k.2.1 x k.2.2 hx0
    exact ⟨ge_of_tendsto (hconv x) (Eventually.of_forall fun k => (hk k).1),
      le_of_tendsto (hconv x) (Eventually.of_forall fun k => (hk k).2)⟩

end FroehlichSpencer.BKT.Provider

end
