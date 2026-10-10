/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.ConditionLambdaFracCorrelation
public import FroehlichSpencer.BKT.Bridge.ConditionLambdaSecondMoment
public import FroehlichSpencer.BKT.Surface.HardCoreFracCorrelation
public import FroehlichSpencer.BKT.Surface.ConditionLambdaGasTheoremAFinite
public import FroehlichSpencer.BKT.Surface.ConditionLambdaGasTheoremBFinite
public import FroehlichSpencer.BKT.Surface.HardCoreGasTheoremAFinite
public import FroehlichSpencer.BKT.Surface.HardCoreGasTheoremBFinite
import Mathlib.Tactic

/-!
# Bridge: the links of the general Coulomb-gas objects

The second moment is not necessarily nonnegative for `β > 0` (FS81 (1.16): "the measure (not
necessarily positive)"), as for source's object.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Bridge.ConditionLambdaLinks

open Filter Topology
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Bridge.ConditionLambdaGas
open FroehlichSpencer.BKT.Bridge.ConditionLambdaFracCorrelation
open FroehlichSpencer.BKT.Bridge.ConditionLambdaSecondMoment

theorem isCoulombGasSummable_hardCore (β z : ℝ) :
    IsCoulombGasSummable β (hardCoreWeightInternal z) := by
  intro Λ t
  refine summable_of_ne_finset_zero (s := chargeConfigsInternal Λ 1) fun q hq => ?_
  obtain ⟨j, hj⟩ : ∃ j, q j ∉ Finset.Icc (-1 : ℤ) 1 := by
    by_contra h
    push Not at h
    exact hq (Fintype.mem_piFinset.2 fun j => by simpa using h j)
  simp only [coulombGasWeight]
  split_ifs
  · rw [Finset.prod_eq_zero (Finset.mem_univ j)
      (Bridge.HardCoreFracCorrelation.hardCoreWeight_eq_zero hj)]
    simp
  · simp

theorem hardCore_nonneg {z : ℝ} (hz : 0 ≤ z) : ∀ q, 0 ≤ hardCoreWeightInternal z q :=
  hardCoreWeight_nonneg hz

theorem hardCore_zero_pos (z : ℝ) : 0 < hardCoreWeightInternal z 0 := by
  rw [Bridge.HardCoreFracCorrelation.hardCoreWeight_zero]; exact one_pos

/-- **(1.23)**: the general correlation at the hard-core law is source's. -/
theorem fracCorrelation_hardCore (β z : ℝ) (hz : 0 ≤ z) (ξ : ℝ) (Λ : Finset (ℤ × ℤ))
    (a b : Λ) :
    conditionLambdaFracCorrelation β (hardCoreWeightInternal z) (hardCore_nonneg hz)
        (hardCore_zero_pos z) (isCoulombGasSummable_hardCore β z) ξ Λ a b =
      hardCoreFracCorrelation β z hz ξ Λ a b := by
  rw [fracCorrelation_eq_region Λ β _ _ _ _ (fun n => hardCoreWeight_neg z n),
    Bridge.HardCoreFracCorrelation.hardCoreFracCorrelation_eq_region]

/-- **(1.16)–(1.17)**: the general second moment at the hard-core law is source's. -/
theorem secondMoment_hardCore (β : ℝ) (hβ : 0 < β) (z : ℝ) (hz : 0 ≤ z) (Λ : Finset (ℤ × ℤ))
    (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ) (hg : (g.sum fun _ a => a) = 0) :
    conditionLambdaSecondMoment β hβ (hardCoreWeightInternal z) (hardCore_nonneg hz)
        (hardCore_zero_pos z) (isCoulombGasSummable_hardCore β z) Λ g hgΛ hg =
      hardCoreSecondMoment β hβ z hz Λ g hgΛ hg := by
  rw [secondMoment_eq_full, Bridge.HardCoreSecondMomentFree.hardCoreSecondMoment_eq_free]
  unfold fullSecondMomentInternal freeSecondMomentInternal fullGasExpectationInternal
    fullGasPartitionInternal freeGasExpectationInternal gasExpectationInternal gasPartitionInternal
  have h1 := Bridge.HardCoreFracCorrelation.tsum_gasWeight_hardCore_mul
    (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β z (fun _ => 1)
  simp only [mul_one] at h1
  rw [Bridge.HardCoreFracCorrelation.tsum_gasWeight_hardCore_mul, h1]
  rfl


theorem secondMoment_iteratedLimit {C α ε β : ℝ} (hβ : 0 < β) {lam : ℤ → ℝ}
    (h : IsConditionLambda C α ε β lam) (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0)
    (hβg : gateThreshold α ε < β) (hS : IsCoulombGasSummable β lam) (Λ : Finset (ℤ × ℤ))
    (g : ℤ × ℤ →₀ ℝ) (hgΛ : g.support ⊆ Λ) (hg : (g.sum fun _ a => a) = 0)
    (root : ∀ n, Fin (torusSideInternal n) × Fin (torusSideInternal n)) :
    (∀ N : ℕ, Tendsto (fun n => weightedGFFExpectation (squarePeriodic (torusSideInternal n))
        (squarePeriodic_connected _ (one_lt_torusSide n)) β⁻¹ (inv_pos.2 hβ) (root n)
        (torusCutoffWeightsInternal (Subtype.val : Λ → ℤ × ℤ) n N (fun m => (lam 0)⁻¹ * lam m))
        (fun φ => (∑ j, φ j * latticePushInternal (torusSideInternal n)
          (Subtype.val : Λ → ℤ × ℤ) (fun v => g v) j) ^ 2))
      atTop (𝓝 (freeCutoffSecondMomentInternal (Subtype.val : Λ → ℤ × ℤ) N β
        (fun m => (lam 0)⁻¹ * lam m) (fun v => g v)))) ∧
    Tendsto (fun N => freeCutoffSecondMomentInternal (Subtype.val : Λ → ℤ × ℤ) N β
        (fun m => (lam 0)⁻¹ * lam m) (fun v => g v)) atTop
      (𝓝 (conditionLambdaSecondMoment β hβ lam hlam hlam0 hS Λ g hgΛ hg)) := by
  have hint := conditionLambdaInternal_normalize h hlam0 le_rfl
  have hphys := physical_normalize hlam hlam0
  have hev : ∀ m, (lam 0)⁻¹ * lam (-m) = (lam 0)⁻¹ * lam m := fun m => by rw [(h.2 m).1]
  have hd : 0 < 1 / 16 - ε := by linarith [h.1]
  have hκα : α < β * (1 / 16 - ε) := by
    have := (div_lt_iff₀ hd).1 hβg
    linarith [le_max_left α 0]
  have hgate : GateInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β
      (fun _ => fun m => (lam 0)⁻¹ * lam m) :=
    gate_of_conditionLambda hβ.le (fun _ => hint)
      (fun q hq => free_chargeEnergy_ge (Subtype.val : Λ → ℤ × ℤ) Subtype.val_injective q hq) hκα
  have hZ : fullGasPartitionInternal (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) β
      (fun _ => fun m => (lam 0)⁻¹ * lam m) ≠ 0 :=
    (lt_of_lt_of_le one_pos (one_le_fullGasPartition hgate.summable (fun _ => hphys.2)
      (fun _ => hphys.1))).ne'
  refine ⟨fun N => tendsto_torus_cutoff_secondMoment _ Subtype.val_injective β hβ N _ hev hphys
    _ (sum_region_eq_zero Λ g hgΛ hg) root, ?_⟩
  rw [secondMoment_eq_full, ← fullSecondMoment_normalize _ _ _ hlam0.ne']
  exact (tendsto_free_cutoff_moments _ β _ hgate hZ (fun v => g v) 0).2

/--
**The general finite Theorem B implies source's  hard-core finite Theorem B.**
-/
theorem hardCoreGasTheoremB_of_general
    (hgen : type_of% @FroehlichSpencer.BKT.conditionLambdaGas_fracCorrelation_upper_bound) :
    type_of% @FroehlichSpencer.BKT.hardCoreGas_fracCorrelation_upper_bound := by
  intro ξ hξ0 hξ1 ε hε
  obtain ⟨β', hβ', hB⟩ := hgen ξ hξ0 hξ1 ε
  refine ⟨β', hβ', fun K => ?_⟩
  obtain ⟨β₀, hB⟩ := hB (max 1 (K / 2)) 0 1 one_pos
  refine ⟨β₀, fun β hβ => ?_⟩
  obtain ⟨A, hA⟩ := hB β hβ
  refine ⟨A, fun z hz hzK Λ h0 x hx hx0 => ?_⟩
  have hcl : IsConditionLambda (max 1 (K / 2)) 0 ε β (hardCoreWeightInternal z) := by
    refine ⟨hε, fun q => ⟨(hardCoreWeight_neg z q).symm, ?_⟩⟩
    have hz2 : z / 2 ≤ max 1 (K / 2) * Real.exp (ε * β) := by
      have := Real.exp_pos (ε * β)
      calc z / 2 ≤ K / 2 * Real.exp (ε * β) := by linarith
        _ ≤ max 1 (K / 2) * Real.exp (ε * β) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) this.le
    unfold hardCoreWeightInternal
    split_ifs with h0' h1
    · subst h0'; simp
    · have hq : (q : ℝ) ^ 2 = 1 := by rcases h1 with rfl | rfl <;> simp
      rw [hq, mul_one, zero_add, abs_of_nonneg (by linarith)]
      exact hz2
    · simp only [abs_zero]; positivity
  obtain ⟨hS, hb⟩ := hA (hardCoreWeightInternal z) hcl (hardCore_nonneg hz)
    (hardCore_zero_pos z) (by rw [Bridge.HardCoreFracCorrelation.hardCoreWeight_zero])
  rw [← fracCorrelation_hardCore β z hz ξ Λ ⟨0, h0⟩ ⟨x, hx⟩]
  exact hb Λ h0 x hx hx0

/--
**The general finite Theorem A implies source's  hard-core finite Theorem A.**
-/
theorem hardCoreGasTheoremA_of_general
    (hgen : type_of% @FroehlichSpencer.BKT.conditionLambdaGas_secondMoment_lower_bound) :
    type_of% @FroehlichSpencer.BKT.hardCoreGas_secondMoment_lower_bound := by
  intro δ hδ α
  obtain ⟨β₀, hA⟩ := hgen δ hδ 1 α (1 / 17) 1 one_pos
  refine ⟨β₀, fun β hβ hβ₀ z hz hzβ Λ g hgΛ hg => ?_⟩
  have hcl : IsConditionLambda 1 α (1 / 17) β (hardCoreWeightInternal z) := by
    refine ⟨by norm_num, fun q => ⟨(hardCoreWeight_neg z q).symm, ?_⟩⟩
    unfold hardCoreWeightInternal
    split_ifs with h0' h1
    · subst h0'; simp
    · have hq : (q : ℝ) ^ 2 = 1 := by rcases h1 with rfl | rfl <;> simp
      rw [hq, mul_one, one_mul, abs_of_nonneg (by linarith)]
      have : β / 17 + α = α + 1 / 17 * β := by ring
      have hexp : Real.exp (β / 17 + α) = Real.exp (α + 1 / 17 * β) := by rw [this]
      have := Real.exp_pos (α + 1 / 17 * β)
      linarith
    · simp only [abs_zero]; positivity
  obtain ⟨hS, hb⟩ := hA β hβ hβ₀ (hardCoreWeightInternal z) hcl (hardCore_nonneg hz)
    (hardCore_zero_pos z) (by rw [Bridge.HardCoreFracCorrelation.hardCoreWeight_zero])
  rw [← secondMoment_hardCore β hβ z hz Λ g hgΛ hg]
  exact hb Λ g hgΛ hg


theorem hardCoreGas_fracCorrelation_upper_bound_of_conditionLambda :
    type_of% @FroehlichSpencer.BKT.hardCoreGas_fracCorrelation_upper_bound :=
  hardCoreGasTheoremB_of_general FroehlichSpencer.BKT.conditionLambdaGas_fracCorrelation_upper_bound


theorem hardCoreGas_secondMoment_lower_bound_of_conditionLambda :
    type_of% @FroehlichSpencer.BKT.hardCoreGas_secondMoment_lower_bound :=
  hardCoreGasTheoremA_of_general FroehlichSpencer.BKT.conditionLambdaGas_secondMoment_lower_bound

end FroehlichSpencer.BKT.Bridge.ConditionLambdaLinks

end
