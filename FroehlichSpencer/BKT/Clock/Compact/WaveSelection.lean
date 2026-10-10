/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.CompositeWave
import Mathlib.Tactic

/-!
# The clock wave selection on KP's square domains
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Compact

open SpinWaves Reduction
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Generic.Marked

section Selection

variable (boundary : SquareBoundary) {L : ℕ} {E : Type} [Fintype E]

/-- **The clock wave selection** with gain `g`: every neutral member `ϱ` of every KP ensemble with
(a)–(c) has a spin wave with the support and constancy clauses of KP P2.4 relative to the
neutral part of its ensemble, whose clock translation energy is at least `g(ϱ)`. -/
def ClockWaveSelection (Λ : Multigraph (Fin L × Fin L) E)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L) (β n : ℝ)
    (g : (Fin L × Fin L → ℤ) → ℝ) : Prop :=
  ∀ N : Finset (Fin L × Fin L → ℤ), IsChargeEnsemble N → AtMostOneNonNeutral N →
    IsScaleSeparated boundary L N → NeutralSplitsAreCharged boundary L N →
    ∀ ϱ ∈ neutralPart N, ∃ a : Fin L × Fin L → ℝ,
      (∀ ϱ' ∈ Λ.comparableDensities (neutralPart N) ϱ,
        ∃ c : ℝ, ∀ j ∈ Λ.densityDomainPlus ϱ' (centerOf ϱ'), a j = c) ∧
      Function.support a ⊆ Λ.densityDomain ϱ (centerOf ϱ) ∧
      g ϱ ≤ translationEnergy (clockShiftCost β n) (gradLinear Λ) a fun j => (ϱ j : ℝ)

/-- **The clock wave selection on KP's square domains**: the envelope waves of the all-scales
graded spin waves (`exists_fullGradedSpinWave`) give the gain
`(λ/8) ∑_j |ϱ(j)| + λ/(8 D₁) A(ϱ)` under the cost-envelope conditions of the T1.6-NG assembly. -/
theorem clockWaveSelection_kp (hL : 1 < L) (Λ : Multigraph (Fin L × Fin L) E)
    (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ) {D₁ : ℝ}
    (hD₁ : 0 < D₁) (h21 : Reduction.P21Step boundary L D₁)
    (centerOf : (Fin L × Fin L → ℤ) → Fin L × Fin L)
    (hcenter : ∀ ϱ : Fin L × Fin L → ℤ, ϱ ≠ 0 → Λ.IsDensityCenter ϱ (centerOf ϱ))
    {β n κ κ' W : ℝ} (hc : IsCostEnvelope (clockShiftCost β n) κ κ' W) (hκ : 0 < κ)
    {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * 28 ≤ W) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * 28) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * 4096))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 28) :
    ClockWaveSelection boundary Λ centerOf β n fun ϱ =>
      amp / 8 * ∑ j, |(ϱ j : ℝ)| + amp / (8 * D₁) * (chargeCoverCost boundary L ϱ : ℝ) := by
  classical
  intro N hens hNa hNb hNc ϱ hϱ
  obtain ⟨Wv, hα, hK₀, hK₁, hbase, hcount, hedge⟩ := exists_fullGradedSpinWave boundary hL Λ hΛ
    hdist B h46 centerOf hcenter N hens hNa hNb hNc ϱ hϱ
  obtain ⟨hϱN, -⟩ := mem_neutralPart.mp hϱ
  have hϱ0 : ϱ ≠ 0 := hens.1 ϱ hϱN
  let _ := Wv.finite
  refine ⟨envelopeWave Wv κ amp k₀, envelopeWave_const_plus Wv κ amp k₀,
    envelopeWave_support_subset Wv κ amp k₀, ?_⟩
  -- the cover bound (KP P2.1)
  have hcover : (chargeCoverCost boundary L ϱ : ℝ) ≤ D₁ * (∑ j, |(ϱ j : ℝ)| +
      ((Finset.univ.filter fun t => 1 ≤ Wv.scale t).card : ℝ)) := by
    have hA := (h21 (fun ϱ k => sharedMinimumSquareCover boundary L ϱ (by omega) k) ϱ hϱ0).2
    have hS0 : (squareCoverNumber boundary L 0 ϱ : ℝ) ≤ ∑ j, |(ϱ j : ℝ)| :=
      (Nat.cast_le.mpr (Reduction.squareCoverNumber_zero_le_card boundary L ϱ)).trans
        (card_chargeSupport_le_sum_abs ϱ)
    rw [hcount]
    calc (chargeCoverCost boundary L ϱ : ℝ)
        ≤ D₁ * (squareCoverNumber boundary L 0 ϱ + separatedSquareTotal boundary L
            (fun ϱ k => sharedMinimumSquareCover boundary L ϱ (by omega) k) ϱ) := hA
      _ ≤ D₁ * (∑ j, |(ϱ j : ℝ)| + separatedSquareTotal boundary L
            (fun ϱ k => sharedMinimumSquareCover boundary L ϱ (by omega) k) ϱ) := by
          gcongr
  -- the envelope gain
  have hα1 : 1 < Wv.alpha := Wv.alpha_gt_one
  have hγ : 0 ≤ gradExponent Wv.alpha := (gradExponent_pos hα1).le
  have hcnt : ∀ t, Wv.scale t < k₀ →
      ((Finset.univ.filter fun e => Λ.grad (Wv.piece t) e ≠ 0).card : ℝ) ≤ 100 * 4 ^ k₀ := by
    intro t ht
    refine (hedge t).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    exact pow_le_pow_right₀ (by norm_num) ht.le
  have hquad : ∀ s, k₀ ≤ s →
      amp ≤ quadAmplitude κ Wv.K₀ Wv.K₁ (gradExponent Wv.alpha) s := by
    intro s hs
    rw [hK₀, hK₁, hα]
    refine le_min hquad₁ (hquad₂.trans ?_)
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [← hα]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hγ
  have hgain := translationEnergy_envelopeWave_ge_gain Wv hc hκ (by rw [hK₀]; norm_num)
    (by rw [hK₁]; norm_num) hamp (by rw [hK₁]; exact hampW) hk₀ hcnt (by rw [hK₁]; exact hexp)
    hquad
  refine le_trans ?_ hgain
  set X : ℝ := ∑ j, |(ϱ j : ℝ)|
  set S : ℝ := ((Finset.univ.filter fun t => 1 ≤ Wv.scale t).card : ℝ)
  set Q : ℝ := ∑ t ∈ Finset.univ.filter (fun t => Wv.scale t = 0), |Wv.charge t|
  have hS : 0 ≤ S := Nat.cast_nonneg _
  have hcov : (chargeCoverCost boundary L ϱ : ℝ) / D₁ ≤ X + S := by
    rw [div_le_iff₀ hD₁]; linarith [hcover]
  have h1 : amp / (8 * D₁) * (chargeCoverCost boundary L ϱ : ℝ) ≤ amp / 8 * (X + S) := by
    rw [show amp / (8 * D₁) * (chargeCoverCost boundary L ϱ : ℝ) =
      amp / 8 * ((chargeCoverCost boundary L ϱ : ℝ) / D₁) by field_simp]
    exact mul_le_mul_of_nonneg_left hcov (by positivity)
  have h2 : (1 / 2 : ℝ) * X ≤ Q := hbase
  nlinarith

end Selection

end FroehlichSpencer.BKT.Clock.Compact

end
