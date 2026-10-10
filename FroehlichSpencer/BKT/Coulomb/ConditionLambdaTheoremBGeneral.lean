/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaTheoremBFullLimit
import Mathlib.Tactic

/-!
# FS81 Theorem B for Condition-λ gases with any positive vacancy weight

What FS81 allows:
- the a-priori measure `dλ` may be any positive measure on `ℤ` (FS81 (1.6)–(1.9), J p. 530);
- Condition λ (a), (b) (J p. 531) asks only evenness and the growth bound.

The roots assume `PhysicalWeightInternal`, i.e. `λ(0) = 1`. That assumption costs nothing,
because the Gibbs state (1.7)–(1.9) is homogeneous of degree zero in `λ`:
* the normalisation `λ ↦ λ/λ(0)` leaves every expectation unchanged
  (`fullGasExpectation_div_const`, `regionCorr_vacancyNormalized`);
* it turns the growth constant `C` into `C/λ(0) ≤ C/ν` (`conditionLambda_vacancyNormalized`).

Roots for nonnegative even laws with a vacancy lower bound `0 < ν ≤ λ(0)`. The bound `ν` is part
of the fixed data `(C, α, ε, ν, η)` that determine `κ₀` (and `R`); `c` and the bounds do not
depend on `ν`.
* **`coulombB_conditionLambda_free_fullRange_general`**;
* **`coulombB_conditionLambda_thermodynamicLimit_fullRange_general`**;
* **`coulombB_conditionLambda_free_fullRange_far_general`**;
* `coulombB_conditionLambda_free_general`: the marked-cluster estimate's restricted κ-uniform form.

Coverage:
- FS81's standard gas (1.11), with `λ(0) = I₀(z) ≥ 1`, is covered with `ν = 1`.
- The case `λ(0) = 0` cannot be included (`ConditionLambdaTheoremBGeneralZeroVacancy`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory Filter Topology FroehlichSpencer.BKT.Generic.Marked

/-! ### Normalising the vacancy weight -/

section Normalization

variable {V : Type*} [Fintype V]

/-- The law normalised by its vacancy weight, `λ/λ(0)`. -/
def vacancyNormalizedInternal (lam : ℤ → ℝ) : ℤ → ℝ := fun n => lam n / lam 0

/-- Dividing the law by `a` divides each gas weight by `a^{|V|}`. -/
theorem gasWeight_div_const (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : ℤ → ℝ) (a : ℝ)
    (q : V → ℤ) :
    gasWeightInternal T κ (fun _ => fun n => lam n / a) q =
      a⁻¹ ^ Fintype.card V * gasWeightInternal T κ (fun _ => lam) q := by
  unfold gasWeightInternal
  split_ifs
  · simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    ring
  · simp

/-- **The Gibbs expectation is homogeneous of degree zero in the law** (FS81 (1.7)–(1.9)):
`⟨F⟩` is unchanged when `λ` is divided by `a ≠ 0`. -/
theorem fullGasExpectation_div_const (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) (lam : ℤ → ℝ)
    (F : (V → ℤ) → ℝ) {a : ℝ} (ha : a ≠ 0) :
    fullGasExpectationInternal T κ (fun _ => fun n => lam n / a) F =
      fullGasExpectationInternal T κ (fun _ => lam) F := by
  unfold fullGasExpectationInternal fullGasPartitionInternal
  simp only [gasWeight_div_const, mul_assoc]
  rw [tsum_mul_left, tsum_mul_left, mul_div_mul_left _ _ (pow_ne_zero _ (inv_ne_zero ha))]

end Normalization

/-- The region correlation is unchanged by the vacancy normalisation `λ ↦ λ/λ(0)`. -/
theorem regionCorr_vacancyNormalized (Λ : Finset (ℤ × ℤ)) (κ : ℝ) (lam : ℤ → ℝ) (ξ : ℝ)
    (x y : ℤ × ℤ) (h0 : lam 0 ≠ 0) :
    regionConditionLambdaFracCorrInternal Λ κ (vacancyNormalizedInternal lam) ξ x y =
      regionConditionLambdaFracCorrInternal Λ κ lam ξ x y := by
  unfold regionConditionLambdaFracCorrInternal
  split_ifs with h
  · unfold freeConditionLambdaFracCorrInternal vacancyNormalizedInternal
    rw [fullGasExpectation_div_const _ _ _ _ h0]
  · rfl

/-- Condition λ with constant `C` and vacancy weight `λ(0) ≥ ν > 0` gives Condition λ with constant
`C/ν` for the normalised law. -/
theorem conditionLambda_vacancyNormalized {C α ε κ ν : ℝ} {lam : ℤ → ℝ}
    (h : ConditionLambdaInternal C α ε κ lam) (hν : 0 < ν) (hν0 : ν ≤ lam 0) :
    ConditionLambdaInternal (C / ν) α ε κ (vacancyNormalizedInternal lam) := by
  have h0 : 0 < lam 0 := hν.trans_le hν0
  have hC := h.const_nonneg
  refine ⟨fun n => by simp [vacancyNormalizedInternal, h.1 n], fun n => ?_⟩
  rw [vacancyNormalizedInternal, abs_div, abs_of_pos h0, div_le_iff₀ h0]
  have hE := Real.exp_pos ((α + ε * κ) * (n : ℝ) ^ 2)
  have hCν : C ≤ C / ν * lam 0 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hν]
    exact mul_le_mul_of_nonneg_left hν0 hC
  calc |lam n| ≤ C * Real.exp ((α + ε * κ) * (n : ℝ) ^ 2) := h.2 n
    _ ≤ C / ν * lam 0 * Real.exp ((α + ε * κ) * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hCν hE.le
    _ = C / ν * Real.exp ((α + ε * κ) * (n : ℝ) ^ 2) * lam 0 := by ring

/-- A nonnegative law with positive vacancy weight normalises to a physical law. -/
theorem physicalWeight_vacancyNormalized {lam : ℤ → ℝ} (hnn : ∀ n, 0 ≤ lam n) (h0 : 0 < lam 0) :
    PhysicalWeightInternal (vacancyNormalizedInternal lam) :=
  ⟨div_self h0.ne', fun n => div_nonneg (hnn n) h0.le⟩

/-! ### Theorem B for nonnegative laws with positive vacancy weight -/

section TheoremB

/-- **FS81 Theorem B for Condition-λ gases with any positive vacancy weight, whole range
`ε < 1/16`, free boundary condition.** The law is only assumed nonnegative and even, with the
growth bound and a vacancy weight `λ(0) ≥ ν`. The lower bound `ν > 0` is part of the fixed data
`(C, α, ε, ν, η)` that determine `κ₀`; `c` and the bound do not depend on `ν`. -/
theorem coulombB_conditionLambda_free_fullRange_general :
    ∃ c : ℝ, 0 < c ∧ ∀ C α ε : ℝ, 0 ≤ C → 0 ≤ α → ε < 1 / 16 → ∀ ν : ℝ, 0 < ν →
      ∀ η : ℝ, 0 < η →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
          ConditionLambdaInternal C α ε κ lam → (∀ n, 0 ≤ lam n) → ν ≤ lam 0 →
          ∀ (Λ : Finset (ℤ × ℤ)) (ξ : ℝ) (x y : ℤ × ℤ),
            x ∈ Λ → y ∈ Λ → x ≠ y → 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
            0 ≤ regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ∧
              regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ≤
                2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * κ) *
                  ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                    (-(c * (1 / 16 - max ε 0) * η ^ 2 * κ))) := by
  obtain ⟨c, hc, h⟩ := coulombB_conditionLambda_free_fullRange
  refine ⟨c, hc, fun C α ε hC hα hε ν hν η hη => ?_⟩
  obtain ⟨κ₀, hκ₀, hF⟩ := h (C / ν) α ε (div_nonneg hC hν.le) hα hε η hη
  refine ⟨κ₀, hκ₀, fun κ hκ lam hlam hnn hν0 Λ ξ x y hx hy hxy hξ0 hξ1 hηξ => ?_⟩
  have h0 : 0 < lam 0 := hν.trans_le hν0
  rw [← regionCorr_vacancyNormalized Λ κ lam ξ x y h0.ne']
  exact hF κ hκ _ (conditionLambda_vacancyNormalized hlam hν hν0)
    (physicalWeight_vacancyNormalized hnn h0) Λ ξ x y hx hy hxy hξ0 hξ1 hηξ

/-- **Every thermodynamic limit point**, for nonnegative laws with vacancy weight `λ(0) ≥ ν > 0`,
in the whole range `ε < 1/16`. -/
theorem coulombB_conditionLambda_thermodynamicLimit_fullRange_general :
    ∃ c : ℝ, 0 < c ∧ ∀ C α ε : ℝ, 0 ≤ C → 0 ≤ α → ε < 1 / 16 → ∀ ν : ℝ, 0 < ν →
      ∀ η : ℝ, 0 < η →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
        ConditionLambdaInternal C α ε κ lam → (∀ n, 0 ≤ lam n) → ν ≤ lam 0 →
        ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
        ∀ x y : ℤ × ℤ, x ≠ y → ∀ Λs : ℕ → Finset (ℤ × ℤ),
          (∀ k, x ∈ Λs k ∧ y ∈ Λs k) →
          (∀ k, 0 ≤ regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ∧
            regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ≤
              2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * κ) *
                (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                  (-(c * (1 / 16 - max ε 0) * η ^ 2 * κ))) ∧
          (∃ ℓ : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
            Tendsto (fun k => regionConditionLambdaFracCorrInternal (Λs (φ k)) κ lam ξ x y)
              atTop (𝓝 ℓ)) ∧
          ∀ ℓ : ℝ, MapClusterPt ℓ atTop
              (fun k => regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y) →
            0 ≤ ℓ ∧ ℓ ≤
              2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * κ) *
                (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                  (-(c * (1 / 16 - max ε 0) * η ^ 2 * κ)) := by
  obtain ⟨c, hc, hfree⟩ := coulombB_conditionLambda_free_fullRange_general
  refine ⟨c, hc, fun C α ε hC hα hε ν hν η hη => ?_⟩
  obtain ⟨κ₀, hκ₀, hF⟩ := hfree C α ε hC hα hε ν hν η hη
  refine ⟨κ₀, hκ₀, fun κ hκκ₀ lam hlam hnn hν0 ξ hξ0 hξ1 hηξ x y hxy Λs hΛs => ?_⟩
  let B : ℝ := 2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * κ) *
    (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
      (-(c * (1 / 16 - max ε 0) * η ^ 2 * κ))
  have hk : ∀ k, 0 ≤ regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ∧
      regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ≤ B := by
    intro k
    exact hF κ hκκ₀ lam hlam hnn hν0 (Λs k) ξ x y (hΛs k).1 (hΛs k).2 hxy hξ0 hξ1 hηξ
  have hmem : ∀ k, regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ∈ Set.Icc 0 B :=
    fun k => hk k
  refine ⟨hk, ?_, fun ℓ hℓ =>
    isClosed_Icc.mem_of_mapClusterPt hℓ (Eventually.of_forall hmem)⟩
  obtain ⟨ℓ, -, φ, hφ, hT⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 B) hmem
  exact ⟨ℓ, φ, hφ, hT⟩

/-- **The κ-uniform prefactor away from the diagonal**, for nonnegative laws with vacancy weight
`λ(0) ≥ ν > 0`: beyond a distance `R(C, α, ε, ν, η)` independent of `κ`,
`G_ξ(x, y) ≤ 2 (|x − y|₁ + 1)^{−(c δ η²/2) κ}`, `δ = 1/16 − max(ε, 0)`. -/
theorem coulombB_conditionLambda_free_fullRange_far_general :
    ∃ c : ℝ, 0 < c ∧ ∀ C α ε : ℝ, 0 ≤ C → 0 ≤ α → ε < 1 / 16 → ∀ ν : ℝ, 0 < ν →
      ∀ η : ℝ, 0 < η →
        ∃ κ₀ R : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
          ConditionLambdaInternal C α ε κ lam → (∀ n, 0 ≤ lam n) → ν ≤ lam 0 →
          ∀ (Λ : Finset (ℤ × ℤ)) (ξ : ℝ) (x y : ℤ × ℤ),
            x ∈ Λ → y ∈ Λ → x ≠ y → 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
            R ≤ (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) : ℝ) →
            0 ≤ regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ∧
              regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ≤
                2 * ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                  (-(c * (1 / 16 - max ε 0) * η ^ 2 / 2 * κ))) := by
  obtain ⟨c, hc, h⟩ := coulombB_conditionLambda_free_fullRange_far
  refine ⟨c, hc, fun C α ε hC hα hε ν hν η hη => ?_⟩
  obtain ⟨κ₀, R, hκ₀, hF⟩ := h (C / ν) α ε (div_nonneg hC hν.le) hα hε η hη
  refine ⟨κ₀, R, hκ₀, fun κ hκ lam hlam hnn hν0 Λ ξ x y hx hy hxy hξ0 hξ1 hηξ hR => ?_⟩
  have h0 : 0 < lam 0 := hν.trans_le hν0
  rw [← regionCorr_vacancyNormalized Λ κ lam ξ x y h0.ne']
  exact hF κ hκ _ (conditionLambda_vacancyNormalized hlam hν hν0)
    (physicalWeight_vacancyNormalized hnn h0) Λ ξ x y hx hy hxy hξ0 hξ1 hηξ hR

/-- **The restricted κ-uniform form (the marked-cluster estimate) for nonnegative laws with vacancy weight `λ(0) ≥ ν > 0`**:
for `ε < η²/128`, `G_ξ(x, y) ≤ 2 (|x − y|₁ + 1)^{−c η² κ}`. -/
theorem coulombB_conditionLambda_free_general :
    ∃ c : ℝ, 0 < c ∧ ∀ C α ε : ℝ, 0 ≤ C → 0 ≤ α → ε < 1 / 16 → ∀ ν : ℝ, 0 < ν →
      ∀ η : ℝ, 0 < η → ε < η ^ 2 / 128 →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
          ConditionLambdaInternal C α ε κ lam → (∀ n, 0 ≤ lam n) → ν ≤ lam 0 →
          ∀ (Λ : Finset (ℤ × ℤ)) (ξ : ℝ) (x y : ℤ × ℤ),
            x ∈ Λ → y ∈ Λ → x ≠ y → 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
            0 ≤ regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ∧
              regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ≤
                2 * ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                  (-(c * η ^ 2 * κ))) := by
  obtain ⟨c, hc, h⟩ := coulombB_conditionLambda_free
  refine ⟨c, hc, fun C α ε hC hα hε ν hν η hη hεη => ?_⟩
  obtain ⟨κ₀, hκ₀, hF⟩ := h (C / ν) α ε (div_nonneg hC hν.le) hα hε η hη hεη
  refine ⟨κ₀, hκ₀, fun κ hκ lam hlam hnn hν0 Λ ξ x y hx hy hxy hξ0 hξ1 hηξ => ?_⟩
  have h0 : 0 < lam 0 := hν.trans_le hν0
  rw [← regionCorr_vacancyNormalized Λ κ lam ξ x y h0.ne']
  exact hF κ hκ _ (conditionLambda_vacancyNormalized hlam hν hν0)
    (physicalWeight_vacancyNormalized hnn h0) Λ ξ x y hx hy hxy hξ0 hξ1 hηξ

end TheoremB

end FroehlichSpencer.BKT.Coulomb

end
